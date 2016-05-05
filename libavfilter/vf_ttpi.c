/*
 * Copyright 2016, Skynav, Inc.
 * Copyright 2016, Stanislaw Jesmanowicz, stan <at> jesmanowicz <dot> com
 *
 * This file is part of FFmpeg.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * @file vf_ttpi.c
 *
 * This is Timed Text Presentation Image archive filter, TTPI.
 * The input for this filter is a TTPI archive that includes
 * an XML based manifest file.
 *
 * The input is designated by specifying one of the following
 * three paths:
 *
 * (1) a path to zip file that contains the TTPI archive, with an entry
 * named manifest.xml at the top level;
 * (2) a path to a directory that contains the TTPI archive, with an
 * entry named manifest.xml at the top level;
 * (3) a path to a manifest file that contains reative path names
 * that designate image files;
 *
 * The manifest file uses a format that consists of a small subset
 * of the Timed Text Markup Language Version 2 (TTML2), specifically:
 *
 * (1) a root element that specifies the dimensions of a root
 * container region, which must correspond to the dimensions (storage
 * resolution) of the related video;
 * (2) a sequence of image elements, each contained in a timed and
 * positioned  div (division) element, where each image element
 * references a PNG image file;
 *
 * The filter composites these images onto the video frames that span
 * the event time(s) for these images.
 *
 * Multiple images may apply to a given video frame, in which case
 * they should not intersect (spatially).
 *
 * The XML manifest file is parsed using the libxml2 library.  Make
 * sure to configue the ffmpeg build with proper options or
 * equivalent:
 *
 * configure \
 * --extra-cflags="-I/usr/include/libxml2 \
 * --extra-ldflags="-lxml2
 *
 * Check these flags using pkg-config as follows:
 *
 * pkg-config --cflags libxml-2.0
 * pkg-config --libs libxml-2.0
 *
 */

#include <stdio.h>
#include <unistd.h>

#include "libavcodec/avcodec.h"
#include "libavformat/avformat.h"
#include "libavutil/avstring.h"
#include "libavutil/imgutils.h"
#include "libavutil/opt.h"
#include "libavutil/parseutils.h"
#include "drawutils.h"
#include "avfilter.h"
#include "internal.h"
#include "formats.h"
#include "video.h"

#include "libavutil/imgutils.h"
#include "lswsutils.h"
#include "lavfutils.h"

#include "libavutil/timecode.h"
#include "libavutil/time_internal.h"

#include <libxml/xmlmemory.h>
#include <libxml/parser.h>

#if CONFIG_ZLIB
#include <zlib.h>
#endif /* CONFIG_ZLIB */

#if HAVE_UNISTD_H
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#endif

#if HAVE_DIRENT_H
#include <dirent.h>
#endif

#include <libgen.h> /* for dirname() */

/**
 * TTPI_Event_s - explain ...
 */
typedef struct TTPI_Event_s
{
    int32_t w, h;   /* extent, image dimensions */
    int32_t x, y;   /* origin, image position */
    int64_t begin;  /* time begin */
    int64_t end;    /* time end */
    char  *image;   /* image file name */
    void  *data;    /* image data (here an avi_frame) */

} TTPI_Event;

typedef struct TTPI_Manifest_s
{
    char *lang;     /* ttpi manifest language */
    int32_t w, h;   /* ttpi manifest extend, destination video dimensions */

    TTPI_Event *events; /* array of events */

    int32_t     count;  /* counter, events count */

} TTPI_Manifest;

typedef struct TTPI_Context_s
{
    const AVClass *class;
    char *file;     /* file path of the ttpi manifest */
    int64_t delayusec; /* time offset to be applied to timestamps in the manifest file, can be negative */
    char *dir;      /* directory where from ttpi manifest was taken */

    TTPI_Manifest *manifest; /* TTPI array taken from TTML2 manifest */

    double frame_time; /* in case video has no timestamps */

    enum AVPixelFormat videoFrameFormat; /* YUV format being used in the raw video */
    int  bitDepth; /*8 or 10, bits per sample per plane */
    int  chromaVertSampling; /* YUV422 -> 0, YUV420 -> 1 */

} TTPI_Context;

/* unzip the content of pkzip archive file to temporary directory */
static char *ttpi_unzip(const char *url, char *url_dir); /* unzip stuff */

/**
 * ttpi_str2xy() - parse a string representing two numbers in form "NNpx NNpx"
 * and returns two integer numbers
*/
static int ttpi_str2xy(const char *str, int *x, int *y)
{
    int ret = 0;
    char px[20], py[20];

    if (str && (ret = sscanf(str, "%s %s", px, py)) < 2)
        return 0;

    if (strstr(px, "px"))
        sscanf(px, "%dpx", x);
    else
        sscanf(px, "%d", x);

    if (strstr(py, "px"))
        sscanf(py, "%dpx", y);
    else
        sscanf(py, "%d", y);

    return 1;
}

/**
 * ttpi_str2pts() - parse a string representing timecode in form "hh:mm:ss.mmm"
 * and returns 64bit integer value in milliseconds. This is compatible with
 * current_pts in AV_TIME_BASE_Q units. N.B. in LIBAVFILTER_VERSION_MAJOR < 6,
 * current_pts = current_pts_us (see: libavfilter/avfilter.h).
 */
static int64_t ttpi_str2pts(const char *str)
{
    int hour = 0, min = 0, sec = 0, msec = 0;
    int64_t usec = 0; /* millisecond (= 1000 microseconds) */
    int ret = 0;

    if (str && (ret = sscanf(str, "%d:%d:%d.%d", &hour, &min, &sec, &msec)) < 4)
        return 0;

    usec = 1000 * ((60 * (hour * 60 + min) + sec) * 1000 + msec); /* makes it usec */

    return usec;
}

/**
 * ttpi_parse_element() - parse XML nodes of XML_ELEMENT_NODE type.
 */
static void ttpi_parse_element(xmlNode *parent, TTPI_Manifest **manifest_p)
{
    TTPI_Manifest *manifest = *manifest_p;
    xmlNode *child = parent->children;
    xmlChar *value = NULL;
    int n = 0;
    int x, y;

    if (!(manifest->events = (TTPI_Event *)
        realloc(manifest->events, manifest->count * sizeof(TTPI_Event))))
    {
        return;
    }

    n = manifest->count - 1;

    if (xmlHasProp(parent, (xmlChar *) "extent"))
    {
        if ((value = xmlGetProp(parent, (xmlChar *) "extent")))
        {
            if ((ttpi_str2xy((char *) value, &x, &y)))
            {
                manifest->events[n].w = x;
                manifest->events[n].h = y;
            }
            xmlFree(value);
        }
    }

    if (xmlHasProp(parent, (xmlChar *) "origin"))
    {
        if ((value = xmlGetProp(parent, (xmlChar *) "origin")))
        {
            if ((ttpi_str2xy((char *) value, &x, &y)))
            {
                manifest->events[n].x = x;
                manifest->events[n].y = y;
            }
            xmlFree(value);
        }
    }
    if (xmlHasProp(parent, (xmlChar *) "begin"))
    {
        if ((value = xmlGetProp(parent, (xmlChar *) "begin")))
        {
            manifest->events[n].begin = ttpi_str2pts((char *) value);
            xmlFree(value);
        }
    }
    if (xmlHasProp(parent, (xmlChar *) "end"))
    {
        if ((value = xmlGetProp(parent, (xmlChar *) "end")))
        {
            manifest->events[n].end = ttpi_str2pts((char *) value);
            xmlFree(value);
        }
    }

    while (child)
    {
        if (child->type == XML_ELEMENT_NODE &&
            !xmlStrcmp(child->name, (xmlChar *) "image"))
        {
            if (xmlHasProp(child, (xmlChar *) "src"))
            {
                if ((value = xmlGetProp(child, (xmlChar *) "src")))
                {
                    manifest->events[n].image = strdup((char *) value);
                    xmlFree(value);
                }
            }
        }

        ttpi_parse_element(child, manifest_p);

        child = child->next;
    }
}

/**
 * ttpi_parse_node() - parses XML nodes recursively.
 */
static void ttpi_parse_node(xmlNode *parent, TTPI_Manifest **manifest_p)
{
    xmlNode *child = parent->children;
    while (child)
    {
        if (child->type == XML_ELEMENT_NODE)
        {
            if (!xmlStrcmp(child->name, (xmlChar *) "div"))
            {
                (*manifest_p)->count++;
                ttpi_parse_element(child, manifest_p);
            }
            else
            {
                ttpi_parse_node(child, manifest_p);
            }
        }
        child = child->next;
    }
}

/**
 * ttpi_read_ttml2_manifest() - reads and parse TTML2 based manifest file.
 */
static TTPI_Manifest *ttpi_read_ttml2_manifest(char *path)
{
    TTPI_Manifest *manifest = NULL;
    xmlDocPtr  doc = NULL;
    xmlNodePtr root = NULL;
    xmlChar *value = NULL;
    int x, y;

    /* read it */

    if ((doc = xmlReadFile(path, NULL, XML_PARSE_RECOVER|XML_PARSE_NOERROR)))
    {
        if (!(root = xmlDocGetRootElement(doc)))
        {
            xmlFreeDoc(doc);
            xmlCleanupParser();
            return NULL;
        }

        if (!(manifest = (TTPI_Manifest *) calloc(1, sizeof(TTPI_Manifest))))
        {
            xmlFreeDoc(doc);
            xmlCleanupParser();
            return NULL;
        }

        if (xmlHasProp(root, (xmlChar *) "lang"))
        {
            if ((value = xmlGetProp(root, (xmlChar *) "lang")))
            {
                manifest->lang = strdup((char *) value);
                xmlFree(value);
            }
        }

        if (xmlHasProp(root, (xmlChar *) "extent"))
        {
            if ((value = xmlGetProp(root, (xmlChar *) "extent")))
            {
                if ((ttpi_str2xy((char *) value, &x, &y)))
                {
                    manifest->w = x;
                    manifest->h = y;
                }
                xmlFree(value);
            }
        }

        manifest->count = 0;

        /* parse file for events (div's) */
        ttpi_parse_node(root, &manifest);

        xmlFreeDoc(doc);
        xmlCleanupParser();
    }
    return manifest;
}

/**
 * ttpi_free() - frees all TTPI_Manifest data.
 */
static void ttpi_free(TTPI_Manifest *manifest)
{
    if (manifest)
    {
        int i;

        for (i = 0; i < manifest->count; i++)
        {
           if (manifest->events[i].image)
               free(manifest->events[i].image);

           if (manifest->events[i].data)
               av_frame_free(((AVFrame **) &manifest->events[i].data));
        }

        if (manifest->lang)
           free(manifest->lang);

        if (manifest->events)
            free(manifest->events);

        free(manifest);
    }
}

/**
 * ttpi_uninit() - clean up all ttpi data
 */
static void ttpi_uninit(AVFilterContext *ctx)
{
    TTPI_Context *s = ctx->priv;

    if (s)
    {
        ttpi_free(s->manifest);

        /* set to NULL, so filter_frame() will bypass the input frame */
        s->manifest = NULL;
    }
}

static av_cold int init(AVFilterContext *ctx)
{
    TTPI_Context *s = ctx->priv;

    if (!s->file)
        av_log(ctx, AV_LOG_VERBOSE, "No manifest file provided.\n");

    return 0;
}

static av_cold void uninit(AVFilterContext *ctx)
{
    ttpi_uninit(ctx);
}

static int config_input(AVFilterLink *inlink)
{
    AVFilterContext *ctx = inlink->dst;
    TTPI_Context  *s = ctx->priv;
    TTPI_Manifest *m = NULL;
    TTPI_Event    *e = NULL;

    AVFrame *frame;
    uint8_t *data[4] = { NULL };
    int linesize[4];

    double xScaleRatio = 1.0, yScaleRatio = 1.0;

    enum AVPixelFormat pngformat, yuvaFormat;
    char *url = NULL;
    char path[2048];
    struct stat st;
    int x, y;
    int w, h;
    int er = 0; /* error flag for sanity check */
    int i, ret = 0;
    char *ext = NULL; /* file extension */
    int nDecodes = 0;
#if CONFIG_ZLIB
    int remove = 0;   /* remove path if taken from zip file */
    char *pre = NULL; /* file extension */
#endif /* CONFIG_ZLIB */

    url = s->file;

    if (!url)
    {
        av_log(ctx, AV_LOG_WARNING, "TTPI filter deactivated (manifest file not provided)!\n");
        ttpi_uninit(ctx);
        return 0;
    }

#if CONFIG_ZLIB
    /* check what kind of file input */
    remove = 0;
    pre = strdup(url);

    /* in case of .zip file, unzip it first to a temprary folder (now in /tmp) */
    if ((ext = strrchr(pre, '.')))
    {
        if (!strcmp(ext, ".zip"))
        {
            if ((url = ttpi_unzip(url, NULL))) // NULL: unzip in /tmp
                remove = 1;
        }
    }
    if (pre)
        free(pre);
#endif /* CONFIG_ZLIB */

#if HAVE_LSTAT

    /* if input is directory, get all from directory */
    /* check file/dir type */

    if (!lstat(url, &st))
    {
        if (S_ISDIR(st.st_mode))
        {
            DIR *dir;

            if (url)
            {
                if ((dir = opendir(url)))
                {
                    struct dirent *xml = NULL;

                    while ((xml = readdir(dir)))
                    {
                        if (!(ext = strrchr(xml->d_name, '.')))
                            continue;

                        if (strcmp(ext, ".xml"))
                           continue;

                        sprintf(path, "%s/%s", url, xml->d_name);

                        /* save directory of manifest file, and manifest file */
                        s->dir  = strdup(url);
                        s->file = strdup(path);

                        if (url)
                            free(url);
                        url = path;
                        break;
                    }
                    closedir(dir);
                }
                else
                    av_log(ctx, AV_LOG_WARNING, "%s cannot open dir: %s\n", "config", url);
            }
            else
                av_log(ctx, AV_LOG_WARNING, "%s no path %s\n", "config", url);
        }
    }
    else
    {
        av_log(ctx, AV_LOG_WARNING, "NO file type: %d (%s)\n", st.st_mode, url);
    }

    /* url is .xml manifest file here */
    if (!(s->manifest = ttpi_read_ttml2_manifest(url)))
    {
        av_log(ctx, AV_LOG_ERROR, "Cannot load the manifest file %s.\n", url);
        ttpi_uninit(ctx);
        return 0;
    }
    /* save directory of manifest file */
    if (!s->dir)
    {
        sprintf(path, "%s", url);
        s->dir = strdup(dirname(path));
    }

#endif /* HAVE_LSTAT */

    if ((s->manifest->w != inlink->w) || (s->manifest->h != inlink->h))
    {
        xScaleRatio = inlink->w * 1.0 / s->manifest->w; //Responsibility of maintaining reasonable bounds is left to the higher application.
        yScaleRatio = inlink->h * 1.0 / s->manifest->h;
    }

    /* in case stream has no timestamps! */
    s->frame_time  = 1.0 /  ((double)inlink->frame_rate.num / inlink->frame_rate.den);
    s->frame_time *= 1000000.0;

    m = s->manifest;

    s->videoFrameFormat = inlink->format;

    /* Check if the input format is supported */
    if( (s->videoFrameFormat != AV_PIX_FMT_YUV420P) &&
        (s->videoFrameFormat != AV_PIX_FMT_YUV422P) &&
        (s->videoFrameFormat != AV_PIX_FMT_YUV420P10LE) &&
        (s->videoFrameFormat != AV_PIX_FMT_YUV422P10LE) )
    {
        av_log(ctx, AV_LOG_ERROR, "TTPI filter: Unsupported video format %d.\n", s->videoFrameFormat);
        ttpi_uninit(ctx);
        return 0;
    }
    else
    {
        switch(s->videoFrameFormat)
        {
        case AV_PIX_FMT_YUV420P:
                 yuvaFormat = AV_PIX_FMT_YUVA420P;
                 s->chromaVertSampling = 1;
                 s->bitDepth = 8;
                 break;
        case AV_PIX_FMT_YUV422P:
                 yuvaFormat = AV_PIX_FMT_YUVA422P;
                 s->chromaVertSampling = 0;
                 s->bitDepth = 8;
                 break;
        case AV_PIX_FMT_YUV420P10LE:
                 yuvaFormat = AV_PIX_FMT_YUVA420P10LE;
                 s->chromaVertSampling = 1;
                 s->bitDepth = 10;
                 break;
        case AV_PIX_FMT_YUV422P10LE:
                 yuvaFormat = AV_PIX_FMT_YUVA422P10LE;
                 s->chromaVertSampling = 0;
                 s->bitDepth = 10;
                 break;
        }
    }

    /* load all images and conver them to yuva frames */
    for (i = 0; i < m->count; i++)
    {
        er = 0; /* for fitting check */

        e = &m->events[i];
        sprintf(path, "%s/%s", s->dir, e->image);

        /* read images (png in this case) using ffmpeg utils (lavfutils.c) */

        if ((ret = ff_load_image(data, linesize, &w, &h, &pngformat, path, ctx)) >= 0)
        {
            /* update decode count for verbose logging */
            ++nDecodes;

            /* update event to accommodate scaling of subtitles */
            if((xScaleRatio != 1.0) || (yScaleRatio != 1.0))
            {
                e->w = (int32_t)(e->w * xScaleRatio) & 0x7FFFFFFE; // Scale and floor to even value (because of YUV420)
                e->h = (int32_t)(e->h * yScaleRatio) & 0x7FFFFFFE;
                e->x = (int32_t)(e->x * xScaleRatio) & 0x7FFFFFFE;
                e->y = (int32_t)(e->y * yScaleRatio) & 0x7FFFFFFE;
            }

            /* one single avframe per image */
            frame = av_frame_alloc();

            /* scale it, but more important - it adds to the frame the apha channel */

            if ((ret = ff_scale_image(frame->data, frame->linesize, e->w, e->h,
                     yuvaFormat, data, linesize, w, h, pngformat, ctx)) < 0)
            {
                av_log(ctx, AV_LOG_ERROR, "Failed to scale image: %s.\n", e->image);
                av_frame_free(&frame);
                ttpi_uninit(ctx);
                return 0;
            }

            /* now check if all that fits in the video frame */
            x = e->x;
            y = e->y;

            if ((x + e->w) >= inlink->w) /* x of image outside the video frame right */
                x = inlink->w - e->w -1, er++;

            if ((y + e->h) >= inlink->h)    /* y of image outside the video frame bottom */
                y = inlink->h - e->h - 1, er++;

            if (x < 0)
                x = 0, er++;

            if (y < 0)
                y = 0, er++;

            if (er)
            {
                av_log(ctx, AV_LOG_ERROR, "image outside the video frame (moved).\n");
                av_log(ctx, AV_LOG_VERBOSE, "%s moved: %d %d -> %d %d\n",
                    e->image, e->x, x, e->y, y);

                e->x = x;
                e->y = y;
            }

            /* add the frame to the events list */
            e->data = (void *) frame;

#if CONFIG_ZLIB
            if (remove) /* was from zip file, remove file */
            {
                if ((er = unlink(path)) != 0)
                    av_log(ctx, AV_LOG_VERBOSE, "rm failed (0x%x): %s\n", er, path);
            }
#endif /* CONFIG_ZLIB */
        }
    }

    av_log(ctx, AV_LOG_VERBOSE, "decoded image count: %d\n", nDecodes);

#if CONFIG_ZLIB
    if (remove) /* was from zip file, remove temporary directory */
    {
       if ((er = unlink(s->file)) != 0)
           av_log(ctx, AV_LOG_VERBOSE, "rm failed (0x%x): %s\n", er, s->file);

       if ((er = rmdir(s->dir)) != 0)
           av_log(ctx, AV_LOG_VERBOSE, "rmdir failed (0x%x): %s\n", er, s->dir);
    }
#endif /* CONFIG_ZLIB */

    return 0;
}

/**
 * ttpi_blend_frame() - copy and blend src image onto dst video frame,
 * with alpha blending
 */
static void ttpi_blend_frame_8bit(
    uint8_t **dst, int *dst_linesize, /* destination frame data */
    uint8_t **src, int *src_linesize, /* source frame data */
    int x, int y,                     /* destination position */
    int w, int h,                     /* source dimentions */
    int chromaVertSampling)           /* Chroma sampled horizontally or not */
{
    int i, j, k;
    int shiftH = 0, shiftV = 0;
    uint8_t *s = NULL; /* source, destination pointer */
    uint8_t *d = NULL; /* source, destination pointer */
    uint8_t *a = NULL; /* alpha value */

    for (i = 0; i < 3; i++) /* planes */
    {
        shiftV = i ? chromaVertSampling : 0;
        shiftH = i ? 1 : 0;

        for (j = 0; j < h; j++) /* rows */
        {
            for (k = 0; k < w; k++) /* columns */
            {
                a = src[3] + (      j         ) * src_linesize[3] + ( k              );
                s = src[i] + (      j >> shiftV) * src_linesize[i] + ( k      >> shiftH);
                d = dst[i] + ((j + y) >> shiftV) * dst_linesize[i] + ((k + x) >> shiftH);

                if (*a == 0xff) /* opaque */
                    *d = *s;
                else
                    *d = (*d * (0x100 - *a) + (*a * *s)) >> 8;
            }
        }
    }
}

/**
 * ttpi_blend_frame() - copy and blend src image onto dst video frame,
 * with alpha blending
 */
static void ttpi_blend_frame_10bit(
    uint8_t **dst, int *dst_linesize, /* destination frame data */
    uint8_t **src, int *src_linesize, /* source frame data */
    int x, int y,                     /* destination position */
    int w, int h,                     /* source dimentions */
    int chromaVertSampling)           /* Chroma sampled horizontally or not */
{
    int i, j, k;
    int shiftH = 0, shiftV = 0;
    uint16_t *s = NULL; /* source, destination pointer */
    uint16_t *d = NULL; /* source, destination pointer */
    uint16_t *a = NULL; /* alpha value */

    for (i = 0; i < 3; i++) /* planes */
    {
        shiftV = i ? chromaVertSampling : 0;
        shiftH = i ? 1 : 0;

        for (j = 0; j < h; j++) /* rows */
        {
            for (k = 0; k < w; k++) /* columns */
            {
                a = ((uint16_t*)(src[3] + (      j         ) * src_linesize[3])) + ( k              );
                s = ((uint16_t*)(src[i] + (      j >> shiftV) * src_linesize[i])) + ( k      >> shiftH);
                d = ((uint16_t*)(dst[i] + ((j + y) >> shiftV) * dst_linesize[i])) + ((k + x) >> shiftH);

                if (*a == 0x3ff) /* opaque */
                    *d = *s;
                else
                    *d = (*d * (0x400 - *a) + (*a * *s)) >> 10;
            }
        }
    }
}


static int filter_frame(AVFilterLink *inlink, AVFrame *frame)
{
    AVFilterContext *ctx = inlink->dst;
    TTPI_Context  *s = inlink->dst->priv;
    TTPI_Manifest *m = NULL;
    TTPI_Event    *e = NULL;
    int64_t pts; /* current time in seconds */
    int i;

#if LIBAVFILTER_VERSION_MAJOR > 5
    pts = inlink->current_pts_us;
#else
    pts = inlink->current_pts;
#endif

    /* it looks like this stream has no timestamps! */
    if (pts == AV_NOPTS_VALUE)
        pts = (int64_t) ((double) inlink->frame_count * s->frame_time);

    if (!s->manifest)
        return ff_filter_frame(inlink->dst->outputs[0], frame);

    m = s->manifest;
    e = &m->events[0];

    for (i = 0; i < m->count; i++)
    {
        e = &m->events[i];

        if ((pts >= (e->begin + s->delayusec)) && (pts < (e->end + s->delayusec)))
        {
            AVFrame *f = (AVFrame *) e->data;

            /* now check if it fits in the video frame */

            if ((e->x + e->w) >= frame->width)  /* image outside the video frame, right */
            {
                av_log(ctx, AV_LOG_ERROR, "image outside the video frame: right.\n");
                continue;
            }

            if ((e->y + e->h) >= frame->height) /* image outside the video frame, bottom */
            {
                av_log(ctx, AV_LOG_ERROR, "image outside the video frame: bottom.\n");
                continue;
            }

            if(s->bitDepth == 8)
            {
                ttpi_blend_frame_8bit(frame->data, frame->linesize, f->data, f->linesize,
                                e->x, e->y, e->w, e->h, s->chromaVertSampling);
            }
            else
            {
                ttpi_blend_frame_10bit(frame->data, frame->linesize, f->data, f->linesize,
                                e->x, e->y, e->w, e->h, s->chromaVertSampling);
            }
        }
    }

    return ff_filter_frame(inlink->dst->outputs[0], frame);
}


#define OFFSET(x) offsetof(TTPI_Context, x)
#define FLAGS AV_OPT_FLAG_VIDEO_PARAM|AV_OPT_FLAG_FILTERING_PARAM

#if CONFIG_TTPI_FILTER

static const AVOption ttpi_options[] =
{
    { "file", "get manifest from file(.xml) or folder.",  OFFSET(file), AV_OPT_TYPE_STRING, {.str=NULL}, .flags = FLAGS },
    { "delayusec", "Optional delay (+/- microseconds) to the time stamps in manifest.", OFFSET(delayusec), AV_OPT_TYPE_INT64, {.i64=0}, .min = -36000000000.0, .max = 36000000000.0, .flags = FLAGS },
    { NULL }
};

AVFILTER_DEFINE_CLASS(ttpi);

static const AVFilterPad ttpi_inputs[] =
{
    {
        .name           = "default",
        .type           = AVMEDIA_TYPE_VIDEO,
        .config_props   = config_input,
        .filter_frame   = filter_frame,
        .needs_writable = 1,
    },
    { NULL }
};

static const AVFilterPad ttpi_outputs[] =
{
    {
        .name = "default",
        .type = AVMEDIA_TYPE_VIDEO,
    },
    { NULL }
};

AVFilter ff_vf_ttpi =
{
    .name          = "ttpi",
    .description   = NULL_IF_CONFIG_SMALL("Overlay input video with images from TTML2 manifest file."),
    .priv_size     = sizeof(TTPI_Context),
    .priv_class    = &ttpi_class,
    .init          = init,
    .uninit        = uninit,
    .inputs        = ttpi_inputs,
    .outputs       = ttpi_outputs,
    .flags         = AVFILTER_FLAG_SUPPORT_TIMELINE_GENERIC
};


#if CONFIG_ZLIB

/* zlib stuff */

#define ZIP_FILE_SIZE 1024
#define ZIP_READ_SIZE 16*1024

/* As https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT */
/* 4.3.7  Local file header structure */

/* make sure it is packed; avoid memery padding, header is loaded in one read */
typedef struct __attribute__ ((__packed__)) pkzip_header_s {
    uint32_t signature;
    uint16_t version;
    uint16_t flags;
    uint16_t compression;
    uint16_t mod_time;
    uint16_t mod_date;
    uint32_t crc32;
    uint32_t compressed_size;
    uint32_t uncompressed_size;
    uint16_t file_name_len;
    uint16_t extra_field_len;
} pkzip_header_t;

/* pass destination parameters */
typedef struct dest_s {
    char *dir;
    char *prefix;
    char *url;
} dest_t;

/* get data and uncompress it using zlib */
static void *pkzip_get_data(FILE *fp, pkzip_header_t *header)
{
    void *data = NULL;
    uint8_t *bytes = NULL;
    uint8_t buffer[ZIP_READ_SIZE];
    long rest_read_compressed, rest_read_uncompressed;
    z_stream strm;
    int ret;

    if (!((header->compression == 0) || (header->compression == 8)))
    {
        /* only deflated or uncompressed supported */
        return NULL;
    }

    if (!(data = calloc(1, header->uncompressed_size)))
    {
        /* cannot calloc data */
        return NULL;
    }

    if (header->compression == 0) /* stored (no compression) */
    {
        if (fread(data, 1, header->uncompressed_size, fp) < header->uncompressed_size)
        {
            /* data read failed */
            free(data);
            return NULL;
        }
    }
    else if (header->compression == 8) /* deflate - use zlib */
    {
        bytes = (uint8_t *) data;
        strm.zalloc = Z_NULL;
        strm.zfree  = Z_NULL;
        strm.opaque = Z_NULL;

        strm.avail_in = 0;
        strm.next_in  = Z_NULL;

        /* inflateInit2 raw data */
        if ((ret = inflateInit2(&strm, -MAX_WBITS)) != Z_OK)
        {
            free(data);
            return NULL;
        }

        /* inflate data */
        for (rest_read_compressed = header->compressed_size,
            rest_read_uncompressed = header->uncompressed_size;
            rest_read_compressed && rest_read_uncompressed && ret != Z_STREAM_END;
            rest_read_compressed -= strm.avail_in)
        {
            strm.avail_in = fread(buffer, 1, (sizeof(buffer) < rest_read_compressed)
                ? sizeof(buffer)
                : rest_read_compressed, fp);

            if (strm.avail_in == 0 || ferror(fp))
            {
                inflateEnd(&strm);
                free(data);
                return NULL;
            }

            strm.next_in = buffer;
            strm.avail_out = rest_read_uncompressed;
            strm.next_out = bytes;

            rest_read_compressed -= strm.avail_in;

            ret = inflate(&strm, Z_NO_FLUSH);

            if (ret == Z_STREAM_ERROR ||
                ret == Z_NEED_DICT ||
                ret == Z_DATA_ERROR ||
                ret == Z_MEM_ERROR)
            {
                inflateEnd(&strm);
                free(data);
                return NULL;
            }

            bytes += rest_read_uncompressed - strm.avail_out;
            rest_read_uncompressed = strm.avail_out;
        }
        inflateEnd(&strm);
    }
    return data;
}

static int pkzip_parse_file(FILE *fp, dest_t *dest)
{
    uint8_t *data = NULL;
    pkzip_header_t header;
    char file[ZIP_FILE_SIZE];
    char path[ZIP_FILE_SIZE*2];
    size_t size = sizeof(pkzip_header_t);
    size_t got = 0;
    FILE *out;
    const char dir_delimter = '/';

    if ((got = fread(&header, 1, size, fp)) < size)
    {
        /* header read failed */
        return -1;
    }

    if (header.flags & 1) /* bit 0 set; we do not process encrypted files */
    {
        /* encrypted file */
        return -1;
    }

    /* if wrong signature or end of headers - return */
    if (header.signature != 0x04034b50) /* 4.3.7 Local file header */
        return -1;

    /* get file name */
    memset(file, 0, ZIP_FILE_SIZE);
    if ((got = fread(file, 1, header.file_name_len, fp)) < header.file_name_len)
    {
        /* file name read failed */
        return -1;
    }

    /* skip extra_field data, if any */
    if (header.extra_field_len)
    {
        if (fseek(fp, header.extra_field_len, SEEK_CUR))
        {
            /* cannot seek */
            return -1;
        }
    }

    if (header.uncompressed_size) /* get data if any */
    {
        if (!(data = (uint8_t *) pkzip_get_data(fp, &header)))
        {
            /* cannot read data */
            return -1;
        }
    }
    if (file[header.file_name_len-1] == dir_delimter)
    {
        file[header.file_name_len-1] = 0; /* remove delimeter */
        sprintf(path, "%s/%s_%s", dest->dir, dest->prefix, file);
        dest->url = strdup(path); /* must be freed on exit */

        if ((mkdir(dest->url, S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH)))
        {
            /* cannot create directory */
            /* may allready exist */
        }
        if (data)
            free(data);
        return 0;
    }

    if (data)
    {
        sprintf(path, "%s/%s_%s", dest->dir, dest->prefix, file);
        if ((out = fopen(path, "wb")) != NULL)
        {
            fwrite(data, 1, header.uncompressed_size, out);
            fclose(out);
        }
        free(data);
    }
    return 0;
}

static char *ttpi_unzip(const char *url, char *url_dir)
{
    FILE *fp;
    dest_t dest;
    int fi = 0;

    if (!(fp = fopen(url, "rb")))
    {
        /* cannot open */
        return NULL;
    }

    /* just generate the name and delete created file */
    dest.prefix = strdup("ttpi_XXXXXX");
    if ((fi = mkstemp(dest.prefix)))
    {
        close(fi);
        unlink(dest.prefix);
    }

    if (url_dir)
        dest.dir = strdup(url_dir);
    else
        dest.dir = strdup("/tmp");

    while (!pkzip_parse_file(fp, &dest))
    ;

    fclose(fp);

    if (dest.prefix)
        free(dest.prefix);

    if (dest.dir)
        free(dest.dir);

    return dest.url;
}

#endif /* CONFIG_ZLIB */

#endif /* CONFIG_TTPI_FILTER */
