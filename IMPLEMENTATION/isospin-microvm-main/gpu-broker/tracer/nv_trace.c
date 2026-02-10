/*
 * NVIDIA Driver Trace Shim
 * 
 * LD_PRELOAD library that intercepts all NVIDIA driver interactions:
 * - open/openat for /dev/nvidia*
 * - ioctl calls on nvidia fds
 * - mmap/munmap on nvidia fds
 * 
 * Outputs trace in JSON format compatible with gpu-broker's trace module.
 * 
 * Usage:
 *   LD_PRELOAD=./libnv_trace.so NV_TRACE_FILE=trace.json nvidia-smi -L
 *   LD_PRELOAD=./libnv_trace.so NV_TRACE_FILE=trace.json python train.py
 * 
 * Environment variables:
 *   NV_TRACE_FILE     - Output file (default: /tmp/nv_trace.json)
 *   NV_TRACE_REDZONE  - Enable red zones on mmap (default: 0)
 *   NV_TRACE_VERBOSE  - Print to stderr as well (default: 0)
 *   NV_TRACE_DATA     - Capture ioctl data (default: 1, 0 for headers only)
 * 
 * Build:
 *   gcc -shared -fPIC -o libnv_trace.so nv_trace.c -ldl -lpthread
 */

#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <dlfcn.h>
#include <pthread.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <linux/ioctl.h>

/* ============================================================================
 * Configuration
 * ============================================================================ */

#define MAX_FDS 1024
#define MAX_MMAPS 4096
#define MAX_DATA_SIZE (64 * 1024)  /* Max ioctl data to capture */
#define RED_ZONE_SIZE 4096

/* NVIDIA ioctl magic */
#define NV_IOCTL_MAGIC 'F'

/* NVIDIA escape codes we care about */
#define NV_ESC_RM_ALLOC_MEMORY      0x27
#define NV_ESC_RM_FREE              0x29
#define NV_ESC_RM_CONTROL           0x2A
#define NV_ESC_RM_ALLOC             0x2B
#define NV_ESC_RM_DUP_OBJECT        0x34
#define NV_ESC_RM_SHARE             0x35
#define NV_ESC_RM_MAP_MEMORY        0x4E
#define NV_ESC_RM_UNMAP_MEMORY      0x4F
#define NV_ESC_CARD_INFO            0xC8
#define NV_ESC_ATTACH_GPUS_TO_FD    0xC9
#define NV_ESC_REGISTER_FD          0xC9
#define NV_ESC_CHECK_VERSION_STR    0xD2
#define NV_ESC_SYS_PARAMS           0xD6
#define NV_ESC_EXPORT_TO_DMABUF_FD  0xD8

/* UVM ioctls */
#define UVM_IOCTL_BASE 0
#define UVM_INITIALIZE          (UVM_IOCTL_BASE + 1)
#define UVM_DEINITIALIZE        (UVM_IOCTL_BASE + 2)

/* ============================================================================
 * Data Structures  
 * ============================================================================ */

/* Track which fds are nvidia devices */
typedef struct {
    int fd;
    char device[64];  /* e.g., "/dev/nvidiactl", "/dev/nvidia0" */
    bool active;
} FdRecord;

/* Track mmap regions */
typedef struct {
    void *user_addr;      /* Address returned to application */
    void *real_addr;      /* Actual mmap base (with red zones) */
    size_t user_size;     /* Size requested by application */
    size_t real_size;     /* Actual size (with red zones) */
    int fd;
    off_t offset;
    uint64_t timestamp_ns;
    bool active;
    bool has_redzone;
} MmapRecord;

/* Global state */
static struct {
    /* File tracking */
    FdRecord fds[MAX_FDS];
    pthread_mutex_t fd_lock;
    
    /* Mmap tracking */
    MmapRecord mmaps[MAX_MMAPS];
    pthread_mutex_t mmap_lock;
    
    /* Trace output */
    FILE *trace_file;
    pthread_mutex_t trace_lock;
    uint64_t start_time_ns;
    uint64_t event_count;
    bool first_event;
    
    /* Configuration */
    bool enable_redzone;
    bool verbose;
    bool capture_data;
    
    /* Initialization */
    bool initialized;
    pthread_once_t init_once;
} g_state = {
    .fd_lock = PTHREAD_MUTEX_INITIALIZER,
    .mmap_lock = PTHREAD_MUTEX_INITIALIZER,
    .trace_lock = PTHREAD_MUTEX_INITIALIZER,
    .init_once = PTHREAD_ONCE_INIT,
};

/* Original function pointers */
static int (*real_open)(const char *pathname, int flags, ...) = NULL;
static int (*real_openat)(int dirfd, const char *pathname, int flags, ...) = NULL;
static int (*real_close)(int fd) = NULL;
static int (*real_ioctl)(int fd, unsigned long request, ...) = NULL;
static void *(*real_mmap)(void *addr, size_t length, int prot, int flags, int fd, off_t offset) = NULL;
static int (*real_munmap)(void *addr, size_t length) = NULL;

/* ============================================================================
 * Utilities
 * ============================================================================ */

static uint64_t get_time_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + ts.tv_nsec;
}

static uint64_t get_timestamp_ns(void) {
    return get_time_ns() - g_state.start_time_ns;
}

static void trace_log(const char *fmt, ...) {
    if (!g_state.verbose) return;
    
    va_list args;
    va_start(args, fmt);
    fprintf(stderr, "[nv_trace] ");
    vfprintf(stderr, fmt, args);
    fprintf(stderr, "\n");
    va_end(args);
}

static bool is_nvidia_device(const char *path) {
    if (!path) return false;
    return strncmp(path, "/dev/nvidia", 11) == 0;
}

static const char *get_escape_name(unsigned int cmd) {
    switch (cmd) {
        case NV_ESC_RM_FREE: return "RM_FREE";
        case NV_ESC_RM_CONTROL: return "RM_CONTROL";
        case NV_ESC_RM_ALLOC: return "RM_ALLOC";
        case NV_ESC_RM_ALLOC_MEMORY: return "RM_ALLOC_MEMORY";
        case NV_ESC_RM_MAP_MEMORY: return "RM_MAP_MEMORY";
        case NV_ESC_RM_UNMAP_MEMORY: return "RM_UNMAP_MEMORY";
        case NV_ESC_RM_DUP_OBJECT: return "RM_DUP_OBJECT";
        case NV_ESC_RM_SHARE: return "RM_SHARE";
        case NV_ESC_CARD_INFO: return "CARD_INFO";
        case NV_ESC_ATTACH_GPUS_TO_FD: return "ATTACH_GPUS_TO_FD";
        case NV_ESC_CHECK_VERSION_STR: return "CHECK_VERSION";
        case NV_ESC_SYS_PARAMS: return "SYS_PARAMS";
        case NV_ESC_EXPORT_TO_DMABUF_FD: return "EXPORT_TO_DMABUF_FD";
        default: return NULL;
    }
}

/* ============================================================================
 * Hex encoding for JSON output
 * ============================================================================ */

static void write_hex(FILE *f, const void *data, size_t len) {
    const uint8_t *bytes = data;
    fputc('"', f);
    for (size_t i = 0; i < len; i++) {
        fprintf(f, "%02x", bytes[i]);
    }
    fputc('"', f);
}

static void write_json_string(FILE *f, const char *s) {
    fputc('"', f);
    while (*s) {
        if (*s == '"' || *s == '\\') fputc('\\', f);
        fputc(*s++, f);
    }
    fputc('"', f);
}

/* ============================================================================
 * FD Tracking
 * ============================================================================ */

static void track_fd(int fd, const char *device) {
    if (fd < 0 || fd >= MAX_FDS) return;
    
    pthread_mutex_lock(&g_state.fd_lock);
    g_state.fds[fd].fd = fd;
    strncpy(g_state.fds[fd].device, device, sizeof(g_state.fds[fd].device) - 1);
    g_state.fds[fd].active = true;
    pthread_mutex_unlock(&g_state.fd_lock);
    
    trace_log("Tracking fd %d -> %s", fd, device);
}

static void untrack_fd(int fd) {
    if (fd < 0 || fd >= MAX_FDS) return;
    
    pthread_mutex_lock(&g_state.fd_lock);
    g_state.fds[fd].active = false;
    pthread_mutex_unlock(&g_state.fd_lock);
}

static bool is_tracked_fd(int fd, char *device_out, size_t device_len) {
    if (fd < 0 || fd >= MAX_FDS) return false;
    
    pthread_mutex_lock(&g_state.fd_lock);
    bool tracked = g_state.fds[fd].active;
    if (tracked && device_out) {
        strncpy(device_out, g_state.fds[fd].device, device_len - 1);
    }
    pthread_mutex_unlock(&g_state.fd_lock);
    
    return tracked;
}

/* ============================================================================
 * Mmap Tracking
 * ============================================================================ */

static MmapRecord *find_mmap_slot(void) {
    for (int i = 0; i < MAX_MMAPS; i++) {
        if (!g_state.mmaps[i].active) {
            return &g_state.mmaps[i];
        }
    }
    return NULL;
}

static MmapRecord *find_mmap_by_addr(void *addr) {
    for (int i = 0; i < MAX_MMAPS; i++) {
        if (g_state.mmaps[i].active && g_state.mmaps[i].user_addr == addr) {
            return &g_state.mmaps[i];
        }
    }
    return NULL;
}

/* ============================================================================
 * Trace Output
 * ============================================================================ */

static void trace_write_event_start(void) {
    pthread_mutex_lock(&g_state.trace_lock);
    if (!g_state.first_event) {
        fprintf(g_state.trace_file, ",\n");
    }
    g_state.first_event = false;
}

static void trace_write_event_end(void) {
    fflush(g_state.trace_file);
    pthread_mutex_unlock(&g_state.trace_lock);
}

static void trace_ioctl(const char *device, unsigned long request,
                        const void *data_before, const void *data_after,
                        size_t data_size, int ret) {
    if (!g_state.trace_file) return;
    
    uint64_t ts = get_timestamp_ns();
    unsigned int cmd = _IOC_NR(request);
    const char *op_name = get_escape_name(cmd);
    
    trace_write_event_start();
    
    fprintf(g_state.trace_file, "    {\n");
    fprintf(g_state.trace_file, "      \"type\": \"ioctl\",\n");
    fprintf(g_state.trace_file, "      \"timestamp_ns\": %lu,\n", ts);
    fprintf(g_state.trace_file, "      \"device\": \"%s\",\n", device);
    fprintf(g_state.trace_file, "      \"cmd\": %u,\n", cmd);
    fprintf(g_state.trace_file, "      \"ioctl_nr\": %lu,\n", request);
    
    if (g_state.capture_data && data_before && data_size > 0) {
        size_t cap_size = data_size < MAX_DATA_SIZE ? data_size : MAX_DATA_SIZE;
        fprintf(g_state.trace_file, "      \"request\": ");
        write_hex(g_state.trace_file, data_before, cap_size);
        fprintf(g_state.trace_file, ",\n");
        
        fprintf(g_state.trace_file, "      \"response\": ");
        write_hex(g_state.trace_file, data_after, cap_size);
        fprintf(g_state.trace_file, ",\n");
    } else {
        fprintf(g_state.trace_file, "      \"request\": \"\",\n");
        fprintf(g_state.trace_file, "      \"response\": \"\",\n");
    }
    
    fprintf(g_state.trace_file, "      \"ret\": %d", ret);
    
    if (op_name) {
        fprintf(g_state.trace_file, ",\n      \"op_name\": \"%s\"\n", op_name);
    } else {
        fprintf(g_state.trace_file, "\n");
    }
    
    fprintf(g_state.trace_file, "    }");
    
    trace_write_event_end();
    
    g_state.event_count++;
    trace_log("ioctl %s cmd=0x%x ret=%d", device, cmd, ret);
}

static void trace_mmap(const char *device, void *addr, size_t length,
                       int prot, int flags, int fd, off_t offset, bool has_redzone) {
    if (!g_state.trace_file) return;
    
    uint64_t ts = get_timestamp_ns();
    
    trace_write_event_start();
    
    fprintf(g_state.trace_file, "    {\n");
    fprintf(g_state.trace_file, "      \"type\": \"mmap\",\n");
    fprintf(g_state.trace_file, "      \"timestamp_ns\": %lu,\n", ts);
    fprintf(g_state.trace_file, "      \"device\": \"%s\",\n", device);
    fprintf(g_state.trace_file, "      \"addr\": %lu,\n", (unsigned long)addr);
    fprintf(g_state.trace_file, "      \"length\": %zu,\n", length);
    fprintf(g_state.trace_file, "      \"prot\": %d,\n", prot);
    fprintf(g_state.trace_file, "      \"flags\": %d,\n", flags);
    fprintf(g_state.trace_file, "      \"fd\": %d,\n", fd);
    fprintf(g_state.trace_file, "      \"offset\": %ld,\n", (long)offset);
    fprintf(g_state.trace_file, "      \"has_redzone\": %s\n", has_redzone ? "true" : "false");
    fprintf(g_state.trace_file, "    }");
    
    trace_write_event_end();
    
    g_state.event_count++;
    trace_log("mmap %s addr=%p len=%zu offset=0x%lx", device, addr, length, offset);
}

static void trace_munmap(void *addr, size_t length, const char *device) {
    if (!g_state.trace_file) return;
    
    uint64_t ts = get_timestamp_ns();
    
    trace_write_event_start();
    
    fprintf(g_state.trace_file, "    {\n");
    fprintf(g_state.trace_file, "      \"type\": \"munmap\",\n");
    fprintf(g_state.trace_file, "      \"timestamp_ns\": %lu,\n", ts);
    fprintf(g_state.trace_file, "      \"addr\": %lu,\n", (unsigned long)addr);
    fprintf(g_state.trace_file, "      \"length\": %zu,\n", length);
    if (device) {
        fprintf(g_state.trace_file, "      \"device\": \"%s\"\n", device);
    } else {
        fprintf(g_state.trace_file, "      \"device\": null\n");
    }
    fprintf(g_state.trace_file, "    }");
    
    trace_write_event_end();
    
    g_state.event_count++;
    trace_log("munmap addr=%p len=%zu", addr, length);
}

static void trace_open(const char *device, int fd) {
    if (!g_state.trace_file) return;
    
    uint64_t ts = get_timestamp_ns();
    
    trace_write_event_start();
    
    fprintf(g_state.trace_file, "    {\n");
    fprintf(g_state.trace_file, "      \"type\": \"open\",\n");
    fprintf(g_state.trace_file, "      \"timestamp_ns\": %lu,\n", ts);
    fprintf(g_state.trace_file, "      \"device\": \"%s\",\n", device);
    fprintf(g_state.trace_file, "      \"fd\": %d\n", fd);
    fprintf(g_state.trace_file, "    }");
    
    trace_write_event_end();
    
    g_state.event_count++;
    trace_log("open %s -> fd %d", device, fd);
}

static void trace_close(const char *device, int fd) {
    if (!g_state.trace_file) return;
    
    uint64_t ts = get_timestamp_ns();
    
    trace_write_event_start();
    
    fprintf(g_state.trace_file, "    {\n");
    fprintf(g_state.trace_file, "      \"type\": \"close\",\n");
    fprintf(g_state.trace_file, "      \"timestamp_ns\": %lu,\n", ts);
    fprintf(g_state.trace_file, "      \"device\": \"%s\",\n", device);
    fprintf(g_state.trace_file, "      \"fd\": %d\n", fd);
    fprintf(g_state.trace_file, "    }");
    
    trace_write_event_end();
    
    g_state.event_count++;
    trace_log("close %s fd %d", device, fd);
}

/* ============================================================================
 * Initialization and Finalization
 * ============================================================================ */

static void init_real_functions(void) {
    real_open = dlsym(RTLD_NEXT, "open");
    real_openat = dlsym(RTLD_NEXT, "openat");
    real_close = dlsym(RTLD_NEXT, "close");
    real_ioctl = dlsym(RTLD_NEXT, "ioctl");
    real_mmap = dlsym(RTLD_NEXT, "mmap");
    real_munmap = dlsym(RTLD_NEXT, "munmap");
    
    if (!real_open || !real_openat || !real_close || 
        !real_ioctl || !real_mmap || !real_munmap) {
        fprintf(stderr, "[nv_trace] ERROR: Failed to resolve libc functions\n");
        abort();
    }
}

static void write_trace_header(void) {
    time_t now = time(NULL);
    char time_str[64];
    strftime(time_str, sizeof(time_str), "%Y-%m-%dT%H:%M:%SZ", gmtime(&now));
    
    fprintf(g_state.trace_file, "{\n");
    fprintf(g_state.trace_file, "  \"metadata\": {\n");
    fprintf(g_state.trace_file, "    \"name\": \"nv_trace\",\n");
    fprintf(g_state.trace_file, "    \"description\": \"LD_PRELOAD trace of NVIDIA driver calls\",\n");
    fprintf(g_state.trace_file, "    \"recorded_at\": \"%s\",\n", time_str);
    fprintf(g_state.trace_file, "    \"duration_ns\": 0,\n");
    fprintf(g_state.trace_file, "    \"pid\": %d,\n", getpid());
    
    /* Try to get command line */
    char cmdline[1024] = {0};
    int cmdline_fd = real_open("/proc/self/cmdline", O_RDONLY);
    if (cmdline_fd >= 0) {
        ssize_t n = read(cmdline_fd, cmdline, sizeof(cmdline) - 1);
        real_close(cmdline_fd);
        if (n > 0) {
            /* Replace nulls with spaces */
            for (ssize_t i = 0; i < n - 1; i++) {
                if (cmdline[i] == '\0') cmdline[i] = ' ';
            }
        }
    }
    
    fprintf(g_state.trace_file, "    \"command\": ");
    write_json_string(g_state.trace_file, cmdline);
    fprintf(g_state.trace_file, "\n");
    fprintf(g_state.trace_file, "  },\n");
    fprintf(g_state.trace_file, "  \"events\": [\n");
    
    fflush(g_state.trace_file);
}

static void write_trace_footer(void) {
    uint64_t duration = get_timestamp_ns();
    
    fprintf(g_state.trace_file, "\n  ]\n");
    fprintf(g_state.trace_file, "}\n");
    
    /* Go back and update duration - this is a bit hacky but works */
    /* For now just leave it as 0, could use a temp file approach */
    
    fflush(g_state.trace_file);
    
    fprintf(stderr, "[nv_trace] Trace complete: %lu events in %.3f ms\n",
            g_state.event_count, duration / 1000000.0);
}

static void do_init(void) {
    init_real_functions();
    
    g_state.start_time_ns = get_time_ns();
    g_state.first_event = true;
    
    /* Read configuration from environment */
    const char *trace_file = getenv("NV_TRACE_FILE");
    if (!trace_file) trace_file = "/tmp/nv_trace.json";
    
    const char *redzone = getenv("NV_TRACE_REDZONE");
    g_state.enable_redzone = redzone && atoi(redzone);
    
    const char *verbose = getenv("NV_TRACE_VERBOSE");
    g_state.verbose = verbose && atoi(verbose);
    
    const char *data = getenv("NV_TRACE_DATA");
    g_state.capture_data = !data || atoi(data);  /* Default: capture data */
    
    /* Open trace file */
    g_state.trace_file = fopen(trace_file, "w");
    if (!g_state.trace_file) {
        fprintf(stderr, "[nv_trace] ERROR: Cannot open %s: %s\n",
                trace_file, strerror(errno));
        return;
    }
    
    write_trace_header();
    
    fprintf(stderr, "[nv_trace] Initialized, tracing to %s\n", trace_file);
    fprintf(stderr, "[nv_trace]   redzone=%d verbose=%d capture_data=%d\n",
            g_state.enable_redzone, g_state.verbose, g_state.capture_data);
    
    g_state.initialized = true;
}

static void ensure_init(void) {
    pthread_once(&g_state.init_once, do_init);
}

__attribute__((destructor))
static void fini(void) {
    if (g_state.trace_file) {
        write_trace_footer();
        fclose(g_state.trace_file);
        g_state.trace_file = NULL;
    }
}

/* ============================================================================
 * Intercepted Functions
 * ============================================================================ */

int open(const char *pathname, int flags, ...) {
    ensure_init();
    
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, mode_t);
        va_end(args);
    }
    
    int fd = real_open(pathname, flags, mode);
    
    if (fd >= 0 && is_nvidia_device(pathname)) {
        track_fd(fd, pathname);
        trace_open(pathname, fd);
    }
    
    return fd;
}

int openat(int dirfd, const char *pathname, int flags, ...) {
    ensure_init();
    
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list args;
        va_start(args, flags);
        mode = va_arg(args, mode_t);
        va_end(args);
    }
    
    int fd = real_openat(dirfd, pathname, flags, mode);
    
    if (fd >= 0 && is_nvidia_device(pathname)) {
        track_fd(fd, pathname);
        trace_open(pathname, fd);
    }
    
    return fd;
}

int close(int fd) {
    ensure_init();
    
    char device[64] = {0};
    bool was_tracked = is_tracked_fd(fd, device, sizeof(device));
    
    if (was_tracked) {
        trace_close(device, fd);
        untrack_fd(fd);
    }
    
    return real_close(fd);
}

int ioctl(int fd, unsigned long request, ...) {
    ensure_init();
    
    va_list args;
    va_start(args, request);
    void *argp = va_arg(args, void *);
    va_end(args);
    
    char device[64] = {0};
    if (!is_tracked_fd(fd, device, sizeof(device))) {
        return real_ioctl(fd, request, argp);
    }
    
    /* Determine data size from ioctl request */
    size_t data_size = _IOC_SIZE(request);
    
    /* Copy data before ioctl (for trace comparison) */
    void *data_before = NULL;
    if (g_state.capture_data && argp && data_size > 0 && data_size <= MAX_DATA_SIZE) {
        data_before = alloca(data_size);
        memcpy(data_before, argp, data_size);
    }
    
    /* Perform the actual ioctl */
    int ret = real_ioctl(fd, request, argp);
    int saved_errno = errno;
    
    /* Record the trace */
    trace_ioctl(device, request, data_before, argp, data_size, ret < 0 ? -saved_errno : ret);
    
    errno = saved_errno;
    return ret;
}

void *mmap(void *addr, size_t length, int prot, int flags, int fd, off_t offset) {
    ensure_init();
    
    char device[64] = {0};
    bool is_nvidia = is_tracked_fd(fd, device, sizeof(device));
    
    if (!is_nvidia || !g_state.enable_redzone) {
        /* Normal mmap */
        void *result = real_mmap(addr, length, prot, flags, fd, offset);
        
        if (is_nvidia && result != MAP_FAILED) {
            /* Track even without redzone */
            pthread_mutex_lock(&g_state.mmap_lock);
            MmapRecord *rec = find_mmap_slot();
            if (rec) {
                rec->user_addr = result;
                rec->real_addr = result;
                rec->user_size = length;
                rec->real_size = length;
                rec->fd = fd;
                rec->offset = offset;
                rec->timestamp_ns = get_timestamp_ns();
                rec->has_redzone = false;
                rec->active = true;
            }
            pthread_mutex_unlock(&g_state.mmap_lock);
            
            trace_mmap(device, result, length, prot, flags, fd, offset, false);
        }
        
        return result;
    }
    
    /* Red-zone mmap: allocate with guard pages */
    size_t total_size = RED_ZONE_SIZE + length + RED_ZONE_SIZE;
    
    /* First, reserve the full range with PROT_NONE */
    void *base = real_mmap(NULL, total_size, PROT_NONE, 
                           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (base == MAP_FAILED) {
        return MAP_FAILED;
    }
    
    /* Map the real region in the middle */
    void *real_region = real_mmap(
        (char *)base + RED_ZONE_SIZE,
        length,
        prot,
        flags | MAP_FIXED,
        fd,
        offset
    );
    
    if (real_region == MAP_FAILED) {
        real_munmap(base, total_size);
        return MAP_FAILED;
    }
    
    /* Track the mapping */
    pthread_mutex_lock(&g_state.mmap_lock);
    MmapRecord *rec = find_mmap_slot();
    if (rec) {
        rec->user_addr = real_region;
        rec->real_addr = base;
        rec->user_size = length;
        rec->real_size = total_size;
        rec->fd = fd;
        rec->offset = offset;
        rec->timestamp_ns = get_timestamp_ns();
        rec->has_redzone = true;
        rec->active = true;
    }
    pthread_mutex_unlock(&g_state.mmap_lock);
    
    trace_mmap(device, real_region, length, prot, flags, fd, offset, true);
    
    trace_log("mmap with redzone: base=%p user=%p size=%zu+%zu+%zu",
              base, real_region, (size_t)RED_ZONE_SIZE, length, (size_t)RED_ZONE_SIZE);
    
    return real_region;
}

int munmap(void *addr, size_t length) {
    ensure_init();
    
    pthread_mutex_lock(&g_state.mmap_lock);
    MmapRecord *rec = find_mmap_by_addr(addr);
    
    if (rec && rec->active) {
        char device[64] = {0};
        is_tracked_fd(rec->fd, device, sizeof(device));
        
        void *real_addr = rec->real_addr;
        size_t real_size = rec->real_size;
        bool has_redzone = rec->has_redzone;
        
        rec->active = false;
        pthread_mutex_unlock(&g_state.mmap_lock);
        
        trace_munmap(addr, length, device[0] ? device : NULL);
        
        if (has_redzone) {
            /* Unmap the whole region including red zones */
            return real_munmap(real_addr, real_size);
        } else {
            return real_munmap(addr, length);
        }
    }
    
    pthread_mutex_unlock(&g_state.mmap_lock);
    
    /* Not a tracked mapping */
    return real_munmap(addr, length);
}

/* ============================================================================
 * Additional interceptors for mmap64 variants
 * ============================================================================ */

void *mmap64(void *addr, size_t length, int prot, int flags, int fd, off_t offset) {
    return mmap(addr, length, prot, flags, fd, offset);
}
