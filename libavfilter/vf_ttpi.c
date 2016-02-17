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
 * The XML manifest file is parsed using the libxml2 library and minizip.
 * Make sure to configue the ffmpeg build with proper options:
 *
 * configure \
 * --extra-cflags="-I/usr/include/libxml2 -I/usr/include/minizip" \
 * --extra-ldflags="-lxml2 -lminizip"
 *
 * Check these flags using pkg-config as follows:
 *
 * pkg-config --cflags libxml-2.0 minizip
 * pkg-config --libs libxml-2.0 minizip
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
#include <minizip/unzip.h>

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
    char *dir;      /* directory where from ttpi manifest was taken */

    TTPI_Manifest *manifest; /* TTPI array taken from TTML2 manifest */

    double frame_time; /* in case video has no timestamps */

} TTPI_Context;

static char *ttpi_unzip(const char *url, char *url_dir); /* miniuzip stuff */

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
    int hour, min, sec, msec;
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

    enum AVPixelFormat format;
    char *url = NULL;
    char path[2048];
    struct stat st;
    int x, y;
    int w, h;
    int er = 0; /* error flag for sanity check */
    int i, ret = 0;
    int remove = 0; /* remove path if taken from zip file */
    char *ext = NULL; /* file extension */
    char *pre = NULL; /* file extension */

    url = s->file;

    if (!url)
    {
        av_log(ctx, AV_LOG_WARNING, "TTPI filter deactivated (manifest file not provided)!\n");
        ttpi_uninit(ctx);
        return 0;
    }

    /* check what kind of file input */
    remove = 0;
    pre = strdup(url);

    /* in case od .zip file, unzip it first to a temprary folder (now in /tmp) */
    if ((ext = strrchr(pre, '.')))
    {
        if (!strcmp(ext, ".zip"))
        {
            if ((url = ttpi_unzip(url, NULL))) /* NULL: unzip in /tmp */
                remove = 1;
        }
    }
    if (pre)
        free(pre);

#if HAVE_LSTAT

    /* if input is directory, get all from directory */
    /* check file/dir type */
    if (!lstat(url, &st))
    {
        if (S_ISDIR(st.st_mode))
        {
            DIR *dir;

            av_log(ctx, AV_LOG_WARNING, "Diectory type: %d (%s)\n", st.st_mode, url);

            if (url && !chdir(url))
            {
            av_log(ctx, AV_LOG_WARNING, "in diectory: (%s)\n", url);
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

                        url = path;

                        av_log(ctx, AV_LOG_WARNING, "will load: %s\n", url);

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

#endif /* HAVE_LSTAT */

    /* save directory of manifest file */
    sprintf(path, "%s", url);
    s->dir = strdup(dirname(path));

    if ((s->manifest->w != inlink->w) || (s->manifest->h != inlink->h))
    {
        av_log(ctx, AV_LOG_ERROR, "Extents of manifest and video differ: %dx%d (%dx%d).\n",
            s->manifest->w, s->manifest->h, inlink->w, inlink->h);
    }

    /* in case stream has no timestamps! */
    s->frame_time  = 1.0 / (double) (inlink->frame_rate.num / inlink->frame_rate.den);
    s->frame_time *= 1000000.0;

    m = s->manifest;

    /* load all images and conver them to yuva frames */
    for (i = 0; i < m->count; i++)
    {
        er = 0; /* for fitting check */

        e = &m->events[i];
        sprintf(path, "%s/%s", s->dir, e->image);

        /* read images (png in this case) using ffmpeg utils (lavfutils.c) */

        if ((ret = ff_load_image(data, linesize, &w, &h, &format, path, ctx)) >= 0)
        {
            /* one single avframe per image */
            frame = av_frame_alloc();

            /* scale it, but more important - it adds to the frame the apha channel */

            if ((ret = ff_scale_image(frame->data, frame->linesize, e->w, e->h,
                AV_PIX_FMT_YUVA420P, data, linesize, w, h, format, ctx)) < 0)
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

            if ((y + h) >= inlink->h)    /* y of image outside the video frame bottom */
                y = inlink->h - h - 1, er++;

            if ((x + e->w) < -inlink->w) /* x of image outside the video frame left  */
                x = 1, er++;

            if ((y + h) < -inlink->h)    /* y of image outside the video frame left  */
                y = 1, er++;
   
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

            if (remove) /* was from zip file, remove file */
            {
                if (!(unlink(path)))
                    av_log(ctx, AV_LOG_VERBOSE, "rm OK: %s\n", path);
                else
                    av_log(ctx, AV_LOG_VERBOSE, "rm NO: %s\n", path);
            }
        }
    }
    if (remove) /* was from zip file, remove temporary directory */
    {
       if (!(rmdir(url)))
           av_log(ctx, AV_LOG_VERBOSE, "rmdir OK: %s\n", s->dir);
       else
           av_log(ctx, AV_LOG_VERBOSE, "rmdir NO: %s\n", s->dir);
    }

    return 0;
}

/**
 * ttpi_blend_frame() - copy and blend src image onto dst video frame,
 * with alpha blending
 */
static void ttpi_blend_frame(
    uint8_t **dst, int *dst_linesize, /* destination frame data */
    uint8_t **src, int *src_linesize, /* source frame data */
    int x, int y,                     /* destination position */
    int w, int h)                     /* source dimentions */
{
    int i, j, k;
    int shift = 0;
    uint8_t *s = NULL; /* source, destination pointer */
    uint8_t *d = NULL; /* source, destination pointer */
    uint8_t *a = NULL; /* alpha value */

    for (i = 0; i < 3; i++) /* planes */
    {
        shift = i ? 1 : 0;

        for (j = 0; j < h; j++) /* rows */
        {
            for (k = 0; k < w; k++) /* columns */
            {
                a = src[3] + j * src_linesize[3] + k;
                s = src[i] + (      j >> shift) * src_linesize[i] + (k       >> shift);
                d = dst[i] + ((j + y) >> shift) * dst_linesize[i] + ((k + x) >> shift);

                if (*a == 0xff) /* opaque */
                    *d = *s;
                else                                  
                    *d = ((255 - *a) * *d + *a * *s) >> 8; /* dst = (reverse alpha) * dst + alpha * src */
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

        if ((pts >= e->begin) && (pts < e->end))
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

            ttpi_blend_frame(frame->data, frame->linesize, f->data, f->linesize,
                e->x, e->y, e->w, e->h);
        }
    }

    return ff_filter_frame(inlink->dst->outputs[0], frame);
}


#define OFFSET(x) offsetof(TTPI_Context, x)
#define FLAGS AV_OPT_FLAG_VIDEO_PARAM|AV_OPT_FLAG_FILTERING_PARAM

#if CONFIG_TTPI_FILTER

static const AVOption ttpi_options[] =
{
    { "file", "get manifest from file(.xml), folder or zipped folder(.zio).",  OFFSET(file), AV_OPT_TYPE_STRING, {.str=NULL}, .flags = FLAGS },
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

/* minizip stuff */

#define ZIP_FILE_SIZE 1024
#define ZIP_READ_SIZE 16*1024

static char *ttpi_unzip(const char *url, char *url_dir)
{
    /* Open the zip file */
    unzFile *zipfile = NULL;
    unz_global_info global_info;
    unz_file_info file_info;

    /* Buffer to hold data read from the zip file. */
    const char dir_delimter = '/'; 
    char read_buffer[ZIP_READ_SIZE];
    char dest[ZIP_FILE_SIZE];
    char file[ZIP_FILE_SIZE];
    size_t file_length;
    FILE *out;
    int error = UNZ_OK;
    uLong i;
    char *dir = NULL;
    char *resp = NULL;
    char *prefix = NULL;

    if (!(zipfile = unzOpen(url)))
    {
        return NULL;
    }

    if (unzGetGlobalInfo(zipfile, &global_info) != UNZ_OK)
    {
        unzClose(zipfile);
        return NULL;
    }

    prefix = strdup("ttpi_XXXXXX");
    i = mkstemp(prefix);

    if (url_dir)               
        dir = strdup(url_dir);
    else
        dir = strdup("/tmp");
 
    /* Loop to extract all files */
    for (i = 0; i < global_info.number_entry; i++)
    {
        /* Get info about current file. */
        memset(file, 0, ZIP_FILE_SIZE);
        if (unzGetCurrentFileInfo(zipfile, &file_info, file, ZIP_FILE_SIZE, NULL, 0, NULL, 0) != UNZ_OK)
        {
            unzClose(zipfile);
            return NULL;
        }

        /* Check if this entry is a directory or file. */
        file_length = strlen(file);
        if (file[file_length-1] == dir_delimter)
        {
            /* Entry is a directory, so create it. */
            sprintf(dest, "%s/%s_%s", dir, prefix, file);

            if ((mkdir(dest, S_IRWXU | S_IRWXG | S_IROTH | S_IXOTH)))
            {
                unzClose(zipfile);
                return NULL;
            }
            resp = strdup(dest);
        }
        else
        {
            /* Entry is a file, so extract it. */
            if (unzOpenCurrentFile(zipfile) != UNZ_OK)
            {
                unzClose(zipfile);
                return NULL;
            }

            /* Open a file to write out the data. */
            sprintf(dest, "%s/%s_%s", dir, prefix, file);
            if (!(out = fopen(dest, "wb")))
            {
                unzCloseCurrentFile(zipfile);
                unzClose(zipfile);
                return NULL;
            }

            error = UNZ_OK;
            do
            {
                if ((error = unzReadCurrentFile(zipfile, read_buffer, ZIP_READ_SIZE)) < 0)
                {
                    unzCloseCurrentFile(zipfile);
                    unzClose(zipfile);
                    return NULL;
                }

                /* Write data to file. */
                if (error > 0)
                {
                    /* You should check return of fwrite... */
                    fwrite(read_buffer, error, 1, out);
                }
            } while (error > 0);

            fclose(out);
        }

        unzCloseCurrentFile(zipfile);

        /* Go the the next entry listed in the zip file. */
        if ((i+1) < global_info.number_entry)
        {
            if (unzGoToNextFile(zipfile) != UNZ_OK)
            {
                unzClose(zipfile);
                return NULL;
            }
        }
    }
    unzClose(zipfile);

    if (prefix)
        free(prefix);

    if (dir)
        free(dir);

    return resp;
}

#endif /* CONFIG_TTPI_FILTER */
