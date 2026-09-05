// SPDX-License-Identifier: GPL-2.0+
/*
 * Copyright (C) 2018 BayLibre, SAS
 * Author: Maxime Jourdan <mjourdan@baylibre.com>
 *
 * The Elementary Stream Parser is a HW bitstream parser.
 * It reads bitstream buffers and feeds them to the VIFIFO
 */

#include <linux/init.h>
#include <linux/ioctl.h>
#include <linux/list.h>
#include <linux/module.h>
#include <linux/reset.h>
#include <linux/interrupt.h>
#include <media/videobuf2-dma-contig.h>
#include <media/v4l2-mem2mem.h>

#include "dos_regs.h"
#include "esparser.h"
#include "vdec_helpers.h"

/* PARSER REGS (CBUS) */
#define PARSER_CONTROL 0x00
	#define ES_PACK_SIZE_BIT	8
	#define ES_WRITE		BIT(5)
	#define ES_SEARCH		BIT(1)
	#define ES_PARSER_START		BIT(0)
#define PARSER_FETCH_ADDR	0x4
#define PARSER_FETCH_CMD	0x8
#define PARSER_CONFIG 0x14
	#define PS_CFG_MAX_FETCH_CYCLE_BIT	0
	#define PS_CFG_STARTCODE_WID_24_BIT	10
	#define PS_CFG_MAX_ES_WR_CYCLE_BIT	12
	#define PS_CFG_PFIFO_EMPTY_CNT_BIT	16
#define PFIFO_WR_PTR 0x18
#define PFIFO_RD_PTR 0x1c
#define PARSER_SEARCH_PATTERN 0x24
	#define ES_START_CODE_PATTERN 0x00000100
#define PARSER_SEARCH_MASK 0x28
	#define ES_START_CODE_MASK	0xffffff00
	#define FETCH_ENDIAN_BIT	27
#define PARSER_INT_ENABLE	0x2c
	#define PARSER_INT_HOST_EN_BIT	8
#define PARSER_INT_STATUS	0x30
	#define PARSER_INTSTAT_SC_FOUND	1
#define PARSER_ES_CONTROL	0x5c
#define PARSER_VIDEO_START_PTR	0x80
#define PARSER_VIDEO_END_PTR	0x84
#define PARSER_VIDEO_WP		0x88
#define PARSER_VIDEO_HOLE	0x90

#define SEARCH_PATTERN_LEN	512
#define VP9_HEADER_SIZE		16

static irqreturn_t esparser_isr(int irq, void *dev)
{
	struct amvdec_core *core = dev;
	u32 int_status;

	int_status = amvdec_read_parser(core, PARSER_INT_STATUS);
	if (!int_status)
		return IRQ_NONE;

	amvdec_write_parser(core, PARSER_INT_STATUS, int_status);

	/* Secure an atomic acquire snapshot to protect against concurrent teardown */
	if (!smp_load_acquire(&core->cur_sess))
		return IRQ_NONE;

	if (int_status & PARSER_INTSTAT_SC_FOUND) {
		amvdec_write_parser(core, PFIFO_RD_PTR, 0);
		amvdec_write_parser(core, PFIFO_WR_PTR, 0);
		/* Signal parser completion. */
		WRITE_ONCE(core->search_done, 1);
		wake_up_interruptible(&core->esparser_wq);
	}

	return IRQ_HANDLED;
}

/*
 * VP9 frame headers need to be appended by a 16-byte long
 * Amlogic custom header
 */
static int vp9_update_header(struct amvdec_core *core, struct vb2_buffer *buf)
{
	u8 *dp;
	u8 marker;
	int dsize;
	int num_frames, cur_frame;
	int cur_mag, mag, mag_ptr;
	int frame_size[8], tot_frame_size[8];
	int total_datasize = 0;
	int new_frame_size;
	unsigned char *old_header = NULL;

	dp = (uint8_t *)vb2_plane_vaddr(buf, 0);
	dsize = vb2_get_plane_payload(buf, 0);

	if (dsize == vb2_plane_size(buf, 0)) {
		dev_warn(core->dev, "%s: unable to update header\n", __func__);
		return 0;
	}

	marker = dp[dsize - 1];
	if ((marker & 0xe0) == 0xc0) {
		num_frames = (marker & 0x7) + 1;
		mag = ((marker >> 3) & 0x3) + 1;
		mag_ptr = dsize - mag * num_frames - 2;
		if (dp[mag_ptr] != marker)
			return 0;

		mag_ptr++;
		for (cur_frame = 0; cur_frame < num_frames; cur_frame++) {
			frame_size[cur_frame] = 0;
			for (cur_mag = 0; cur_mag < mag; cur_mag++) {
				frame_size[cur_frame] |=
					(dp[mag_ptr] << (cur_mag * 8));
				mag_ptr++;
			}
			if (cur_frame == 0)
				tot_frame_size[cur_frame] =
					frame_size[cur_frame];
			else
				tot_frame_size[cur_frame] =
					tot_frame_size[cur_frame - 1] +
					frame_size[cur_frame];
			total_datasize += frame_size[cur_frame];
		}
	} else {
		num_frames = 1;
		frame_size[0] = dsize;
		tot_frame_size[0] = dsize;
		total_datasize = dsize;
	}

	new_frame_size = total_datasize + num_frames * VP9_HEADER_SIZE;

	if (new_frame_size >= vb2_plane_size(buf, 0)) {
		dev_warn(core->dev, "%s: unable to update header\n", __func__);
		return 0;
	}

	for (cur_frame = num_frames - 1; cur_frame >= 0; cur_frame--) {
		int framesize = frame_size[cur_frame];
		int framesize_header = framesize + 4;
		int oldframeoff = tot_frame_size[cur_frame] - framesize;
		int outheaderoff =  oldframeoff + cur_frame * VP9_HEADER_SIZE;
		u8 *fdata = dp + outheaderoff;
		u8 *old_framedata = dp + oldframeoff;

		memmove(fdata + VP9_HEADER_SIZE, old_framedata, framesize);

		fdata[0] = (framesize_header >> 24) & 0xff;
		fdata[1] = (framesize_header >> 16) & 0xff;
		fdata[2] = (framesize_header >> 8) & 0xff;
		fdata[3] = (framesize_header >> 0) & 0xff;
		fdata[4] = ((framesize_header >> 24) & 0xff) ^ 0xff;
		fdata[5] = ((framesize_header >> 16) & 0xff) ^ 0xff;
		fdata[6] = ((framesize_header >> 8) & 0xff) ^ 0xff;
		fdata[7] = ((framesize_header >> 0) & 0xff) ^ 0xff;
		fdata[8] = 0;
		fdata[9] = 0;
		fdata[10] = 0;
		fdata[11] = 1;
		fdata[12] = 'A';
		fdata[13] = 'M';
		fdata[14] = 'L';
		fdata[15] = 'V';

		if (!old_header) {
			/* nothing */
		} else if (old_header > fdata + 16 + framesize) {
			dev_dbg(core->dev, "%s: data has gaps, setting to 0\n",
				__func__);
			memset(fdata + 16 + framesize, 0,
			       (old_header - fdata + 16 + framesize));
		} else if (old_header < fdata + 16 + framesize) {
			dev_err(core->dev, "%s: data overwritten\n", __func__);
		}
		old_header = fdata;
	}

	return new_frame_size;
}

/*
 * Pad the packet to at least 4KiB bytes otherwise the VDEC unit won't
 * trigger ISRs. Also append a start code 000001ff at the end to trigger
 * the ESPARSER interrupt.
 */
static int esparser_pad_start_code(struct amvdec_core *core,
				   struct vb2_buffer *vb,
				   u32 payload_size, u32 *pad_size)
{
	u32 plane_size = vb2_plane_size(vb, 0);
	u8 *vaddr = vb2_plane_vaddr(vb, 0);
	u32 padding = 0;

	if (payload_size < ESPARSER_MIN_PACKET_SIZE)
		padding = ESPARSER_MIN_PACKET_SIZE - payload_size;

	if (payload_size > plane_size ||
	    padding > plane_size - payload_size ||
	    SEARCH_PATTERN_LEN >
	    plane_size - payload_size - padding) {
		dev_warn(core->dev,
			 "%s: insufficient plane space: payload=%u pad=%u search=%u plane=%u\n",
			 __func__, payload_size, padding,
			 SEARCH_PATTERN_LEN, plane_size);
		return -ENOSPC;
	}

	if (!vaddr)
		return -EINVAL;

	if (padding)
		memset(vaddr + payload_size, 0, padding);

	memset(vaddr + payload_size + padding, 0, SEARCH_PATTERN_LEN);

	vaddr[payload_size + padding] = 0x00;
	vaddr[payload_size + padding + 1] = 0x00;
	vaddr[payload_size + padding + 2] = 0x01;
	vaddr[payload_size + padding + 3] = 0xff;

	*pad_size = padding;

	return 0;
}

static int
esparser_write_data(struct amvdec_core *core, dma_addr_t addr, u32 size)
{
	u32 parser_ctrl, fetch_cmd;
	long ret;

	if (size > U32_MAX - SEARCH_PATTERN_LEN)
		return -EOVERFLOW;

	mutex_lock(&core->esparser_lock);

	/*
	 * Clear the previous operation before starting a new one.
	 */
	WRITE_ONCE(core->search_done, 0);

	amvdec_write_parser(core, PFIFO_RD_PTR, 0);
	amvdec_write_parser(core, PFIFO_WR_PTR, 0);

	parser_ctrl = ES_WRITE | ES_PARSER_START | ES_SEARCH |
		(size << ES_PACK_SIZE_BIT);

	fetch_cmd = (7 << FETCH_ENDIAN_BIT) |
		(size + SEARCH_PATTERN_LEN);

	amvdec_write_parser(core, PARSER_CONTROL, parser_ctrl);
	amvdec_write_parser(core, PARSER_FETCH_ADDR, addr);

	/*
	 * Ensure the control/address writes are visible before FETCH_CMD
	 * starts the operation.
	 */
	wmb();

	/*
	 * FETCH_CMD starts the parser operation.
	 */
	amvdec_write_parser(core, PARSER_FETCH_CMD, fetch_cmd);

	ret = wait_event_interruptible_timeout(core->esparser_wq,
					       READ_ONCE(core->search_done),
					       HZ / 5);

	if (ret == 0) {
		dev_err(core->dev, "esparser: Bus Master DMA hardware timeout (%u bytes)\n",
			size);

		amvdec_write_parser(core, PARSER_FETCH_CMD, 0);
		amvdec_write_parser(core, PARSER_CONTROL, 0);

		ret = -ETIMEDOUT;
	} else if (ret == -ERESTARTSYS) {
		ret = -ERESTARTSYS;
	} else {
		ret = 0;
	}

	mutex_unlock(&core->esparser_lock);

	return ret;
}

static u32 esparser_vififo_get_free_space(struct amvdec_session *sess)
{
	struct amvdec_core *core = sess->core;
	struct amvdec_ops *vdec_ops = sess->fmt_out->vdec_ops;
	u32 raw_level, fifo_level, hole, usage;

	raw_level = vdec_ops->vififo_level(sess);

	fifo_level = raw_level & GENMASK(23, 0);

	hole = amvdec_read_parser(core, PARSER_VIDEO_HOLE);

	/* Avoid overflow when accounting for the parser hole. */
	if (fifo_level > U32_MAX - hole)
		return 0;

	usage = fifo_level + hole;

	/* Avoid overflow when accounting for the internal FIFO reservation. */
	if (usage > U32_MAX - (6 * SZ_1K))
		return 0;

	usage += 6 * SZ_1K;

	if (usage >= sess->vififo_size) {
		dev_dbg_ratelimited(core->dev,
				    "esparser: VIFIFO full: raw=0x%08x level=%u hole=%u reserved=%u size=%u\n",
				    raw_level, fifo_level, hole,
				    6 * SZ_1K, sess->vififo_size);
		return 0;
	}

	return sess->vififo_size - usage;
}

int esparser_queue_eos(struct amvdec_core *core, const u8 *data, u32 len)
{
	struct device *dev = core->dev;
	void *eos_vaddr;
	dma_addr_t eos_paddr;
	size_t total_len;
	int ret;

	if (!data)
		return -EINVAL;

	if (len > U32_MAX - SEARCH_PATTERN_LEN) {
		dev_err_ratelimited(core->dev,
				    "esparser EOS: data length %u overflows search pattern length\n",
				    len);
		return -EOVERFLOW;
	}

	total_len = len + SEARCH_PATTERN_LEN;

	eos_vaddr = dma_alloc_coherent(dev, total_len,
				       &eos_paddr, GFP_KERNEL);
	if (!eos_vaddr)
		return -ENOMEM;

	memcpy(eos_vaddr, data, len);
	memset((u8 *)eos_vaddr + len, 0, SEARCH_PATTERN_LEN);

	ret = esparser_write_data(core, eos_paddr, len);

	dma_free_coherent(dev, total_len, eos_vaddr, eos_paddr);

	return ret;
}

static u32 esparser_get_offset(struct amvdec_session *sess)
{
	struct amvdec_core *core = sess->core;
	u32 offset = amvdec_read_parser(core, PARSER_VIDEO_WP) -
		     sess->vififo_paddr;

	if (offset < sess->last_offset)
		sess->wrap_count++;

	sess->last_offset = offset;
	offset += (sess->wrap_count * sess->vififo_size);

	return offset;
}

static int
esparser_queue(struct amvdec_session *sess, struct vb2_v4l2_buffer *vbuf)
{
	struct vb2_buffer *vb = &vbuf->vb2_buf;
	struct amvdec_core *core = sess->core;
	struct amvdec_codec_ops *codec_ops = sess->fmt_out->codec_ops;
	u32 payload_size = vb2_get_plane_payload(vb, 0);
	u32 plane_size = vb2_plane_size(vb, 0);
	u32 total_size, free_space, offset;
	u32 num_dst_bufs = 0, pad_size;
	dma_addr_t phy = vb2_dma_contig_plane_dma_addr(vb, 0);
	int ret;

	/*
	 * Check whether enough destination buffers are available before
	 * modifying the source buffer.
	 */
	if (sess->fmt_out->pixfmt == V4L2_PIX_FMT_VP9) {
		if (codec_ops->num_pending_bufs)
			num_dst_bufs = codec_ops->num_pending_bufs(sess);

		num_dst_bufs +=
			v4l2_m2m_num_dst_bufs_ready(sess->m2m_ctx);

		if (num_dst_bufs >= 3)
			num_dst_bufs -= 3;
		else
			num_dst_bufs = 0;

		if (atomic_read(&sess->esparser_queued_bufs) >= num_dst_bufs) {
			dev_dbg_ratelimited(core->dev,
					    "esparser: VP9 destination buffers full (queued=%d available=%u)\n",
					    atomic_read(&sess->esparser_queued_bufs),
					    num_dst_bufs);
			return -EAGAIN;
		}
	}

	/*
	 * Validate the required padding and append the parser start code.
	 */
	ret = esparser_pad_start_code(core, vb, payload_size, &pad_size);
	if (ret) {
		dev_err(core->dev, "esparser: pad start code failed (%d)\n",
			ret);
		return ret;
	}

	/*
	 * Protect the size calculation against overflow.
	 */
	if (payload_size > U32_MAX - pad_size)
		return -EOVERFLOW;

	total_size = payload_size + pad_size;

	/*
	 * esparser_write_data() causes the parser to fetch additional
	 * SEARCH_PATTERN_LEN bytes for start-code detection.
	 */
	if (plane_size < SEARCH_PATTERN_LEN ||
	    total_size > plane_size - SEARCH_PATTERN_LEN) {
		dev_err(core->dev,
			"esparser: frame exceeds plane bounds (payload=%u pad=%u total=%u plane=%u)\n",
			payload_size, pad_size, total_size, plane_size);
		return -EINVAL;
	}

	/*
	 * VP9 header insertion increases the amount of data submitted to
	 * the parser. Reserve space for the maximum possible number of
	 * VP9 frame headers before modifying the buffer.
	 *
	 * A VP9 superframe can contain at most eight frames.
	 */
	if (sess->fmt_out->pixfmt == V4L2_PIX_FMT_VP9) {
		u32 max_size;

		if (payload_size >
		    U32_MAX - (8 * VP9_HEADER_SIZE) - pad_size)
			return -EOVERFLOW;

		max_size = payload_size + 8 * VP9_HEADER_SIZE + pad_size;

		free_space = esparser_vififo_get_free_space(sess);
		if (free_space < max_size) {
			dev_dbg_ratelimited(core->dev,
					    "esparser: VIFIFO backpressure (free=%u need=%u)\n",
					    free_space, max_size);
			return -EAGAIN;
		}

		/*
		 * The FIFO has enough room for the worst-case expanded VP9
		 * frame, so it is now safe to modify the source buffer.
		 */
		ret = vp9_update_header(core, vb);
		if (ret < 0) {
			dev_err_ratelimited(core->dev,
					    "esparser: VP9 parsing error (%d)\n",
					    ret);
			return ret;
		}

		if (ret == 0) {
			dev_err(core->dev,
				"esparser: VP9 header update failed\n");
			return -EBADMSG;
		}

		payload_size = ret;

		/*
		 * Recalculate the padding and append the parser start code
		 * after VP9 header insertion.
		 */
		ret = esparser_pad_start_code(core, vb, payload_size,
					      &pad_size);
		if (ret) {
			dev_err(core->dev, "esparser: pad start code failed (%d)\n",
				ret);
			return ret;
		}

		if (payload_size > U32_MAX - pad_size)
			return -EOVERFLOW;

		total_size = payload_size + pad_size;

		/*
		 * The worst-case check above guarantees this should fit, but
		 * use the actual expanded size for the final check.
		 */
		free_space = esparser_vififo_get_free_space(sess);
		if (free_space < total_size) {
			dev_err(core->dev,
				"esparser: VIFIFO space changed during VP9 setup (free=%u need=%u)\n",
				free_space, total_size);
			return -EAGAIN;
		}
	} else {
		/*
		 * For non-VP9 formats the payload is not modified, so the
		 * exact parser input size can be checked directly.
		 */
		free_space = esparser_vififo_get_free_space(sess);
		if (free_space < total_size) {
			dev_dbg_ratelimited(core->dev,
					    "esparser: VIFIFO backpressure (free=%u need=%u)\n",
					    free_space, total_size);
			return -EAGAIN;
		}
	}

	/*
	 * Capture the parser write position before registering the timestamp.
	 */
	offset = esparser_get_offset(sess);

	ret = amvdec_add_ts(sess, vb->timestamp, vbuf->timecode, offset,
			    vbuf->flags);
	if (ret)
		return ret;

	dev_dbg(core->dev,
		"esparser: ts=%llu payload=%u pad=%u total=%u offset=%08X flags=%08X\n",
		vb->timestamp, payload_size, pad_size, total_size,
		offset, vbuf->flags);

	vbuf->flags = 0;
	vbuf->field = V4L2_FIELD_NONE;
	vbuf->sequence = sess->sequence_out++;

	/*
	 * Submit the complete padded buffer to the parser.
	 */
	ret = esparser_write_data(core, phy, total_size);
	if (ret < 0) {
		dev_warn(core->dev,
			 "esparser: input parsing hardware error: %d\n",
			 ret);

		/*
		 * The timestamp was registered before hardware submission,
		 * so remove it when submission fails.
		 */
		amvdec_remove_ts(sess, vb->timestamp);

		return ret;
	}

	atomic_inc(&sess->esparser_queued_bufs);

	return 0;
}

void esparser_queue_all_src(struct work_struct *work)
{
	struct amvdec_session *sess =
		container_of(work, struct amvdec_session, esparser_queue_work);
	struct amvdec_core *core = sess->core;
	struct device *dev = core->dev_dec;

	while (!READ_ONCE(sess->should_stop)) {
		struct vb2_v4l2_buffer *vbuf;
		bool is_last_buf;
		int ret;

		/* Stop when there are no source buffers to process. */
		mutex_lock(&sess->lock);
		vbuf = v4l2_m2m_next_src_buf(sess->m2m_ctx);
		mutex_unlock(&sess->lock);

		if (!vbuf)
			break;

		is_last_buf = vbuf->flags & V4L2_BUF_FLAG_LAST;

		/*
		 * Keep the buffer queued when the parser cannot accept it.
		 */
		ret = esparser_queue(sess, vbuf);

		/*
		 * The VIFIFO is full. Keep the buffer queued so it can be
		 * processed when space becomes available.
		 */
		if (ret == -EAGAIN)
			break;

		/* Remove the processed buffer before completing it. */
		mutex_lock(&sess->lock);
		v4l2_m2m_src_buf_remove_by_buf(sess->m2m_ctx, vbuf);
		mutex_unlock(&sess->lock);

		if (ret) {
			dev_err_ratelimited(dev,
					    "esparser: parser error %d, dropping buffer\n",
					    ret);
			v4l2_m2m_buf_done(vbuf, VB2_BUF_STATE_ERROR);
		} else {
			v4l2_m2m_buf_done(vbuf, VB2_BUF_STATE_DONE);
		}

		if (is_last_buf)
			break;

		/* Allow other tasks to run between buffer submissions. */
		cond_resched();
	}

	/*
	 * The M2M job remains active while the parser work is running.
	 * Complete it only after all currently available source buffers
	 * have been processed.
	 */
	v4l2_m2m_job_finish(sess->core->m2m_dev, sess->m2m_ctx);
}

int esparser_power_up(struct amvdec_session *sess)
{
	struct amvdec_core *core = sess->core;
	struct amvdec_ops *vdec_ops = sess->fmt_out->vdec_ops;

	mutex_lock(&core->esparser_lock);

	reset_control_reset(core->esparser_reset);
	amvdec_write_parser(core, PARSER_CONFIG,
			    (10 << PS_CFG_PFIFO_EMPTY_CNT_BIT) |
			    (1  << PS_CFG_MAX_ES_WR_CYCLE_BIT) |
			    (16 << PS_CFG_MAX_FETCH_CYCLE_BIT));

	amvdec_write_parser(core, PFIFO_RD_PTR, 0);
	amvdec_write_parser(core, PFIFO_WR_PTR, 0);

	amvdec_write_parser(core, PARSER_SEARCH_PATTERN,
			    ES_START_CODE_PATTERN);
	amvdec_write_parser(core, PARSER_SEARCH_MASK, ES_START_CODE_MASK);

	amvdec_write_parser(core, PARSER_CONFIG,
			    (10 << PS_CFG_PFIFO_EMPTY_CNT_BIT) |
			    (1  << PS_CFG_MAX_ES_WR_CYCLE_BIT) |
			    (16 << PS_CFG_MAX_FETCH_CYCLE_BIT) |
			    (2  << PS_CFG_STARTCODE_WID_24_BIT));

	amvdec_write_parser(core, PARSER_VIDEO_START_PTR, sess->vififo_paddr);
	amvdec_write_parser(core, PARSER_VIDEO_END_PTR,
			    sess->vififo_paddr + sess->vififo_size - 8);
	amvdec_write_parser(core, PARSER_ES_CONTROL,
			    amvdec_read_parser(core, PARSER_ES_CONTROL) & ~1);

	if (vdec_ops->conf_esparser)
		vdec_ops->conf_esparser(sess);

	/* Clear pending parser interrupts before enabling them. */
	amvdec_write_parser(core, PARSER_INT_STATUS, 0xffff);
	amvdec_write_parser(core, PARSER_INT_ENABLE,
			    BIT(PARSER_INT_HOST_EN_BIT));

	/* Start parser after the complete configuration is in place. */
	amvdec_write_parser(core, PARSER_CONTROL,
			    ES_SEARCH | ES_PARSER_START);

	mutex_unlock(&core->esparser_lock);

	return 0;
}

int esparser_power_down(struct amvdec_session *sess)
{
	struct amvdec_core *core = sess->core;

	mutex_lock(&core->esparser_lock);

	amvdec_write_parser(core, PARSER_INT_ENABLE, 0);
	amvdec_write_parser(core, PARSER_CONTROL, 0);
	amvdec_write_parser(core, PARSER_INT_STATUS, 0xffff);
	amvdec_write_parser(core, PFIFO_RD_PTR, 0);
	amvdec_write_parser(core, PFIFO_WR_PTR, 0);
	reset_control_reset(core->esparser_reset);

	mutex_unlock(&core->esparser_lock);

	return 0;
}

int esparser_init(struct platform_device *pdev, struct amvdec_core *core)
{
	struct device *dev = &pdev->dev;
	int ret;

	core->esparser_irq = platform_get_irq_byname(pdev, "esparser");
	if (core->esparser_irq < 0)
		return core->esparser_irq;

	ret = devm_request_irq(dev, core->esparser_irq, esparser_isr,
			       IRQF_SHARED, "esparserirq", core);
	if (ret) {
		dev_err(dev, "Failed requesting ESPARSER IRQ\n");
		return ret;
	}

	core->esparser_reset =
		devm_reset_control_get_exclusive(dev, "esparser");
	if (IS_ERR(core->esparser_reset)) {
		dev_err(dev, "Failed to get esparser_reset\n");
		return PTR_ERR(core->esparser_reset);
	}

	return 0;
}
