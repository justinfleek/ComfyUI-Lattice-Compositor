/*
 * SPDX-FileCopyrightText: Copyright (c) 2026 Isospin Authors
 * SPDX-License-Identifier: MIT
 *
 * nvidia-shim.ko - GPU broker shim for ioctl forwarding
 *
 * This module intercepts NVIDIA ioctls and forwards them to the GPU broker
 * via vsock. It can be built in two modes:
 *
 * GUEST MODE (default, NV_SHIM_HOST=0):
 *   Runs in a VM without GPU access. Forwards ioctls to broker on host.
 *   Host has real GPU, guest has this shim.
 *
 *       Guest VM                          Host
 *       ────────                          ────
 *       CUDA app                          gpu-broker
 *           ↓                                 ↓
 *       nvidia-shim.ko ───vsock CID=2───► real nvidia.ko
 *           ↓                                 ↓
 *       /dev/nvidiactl (fake)             /dev/nvidiactl (real)
 *
 * HOST MODE (NV_SHIM_HOST=1):
 *   Runs on host. Forwards ioctls to broker inside a VM that has the real GPU.
 *   This is the "GPU server" model where the VM owns the GPU.
 *
 *       Host                              Guest VM (VFIO GPU)
 *       ────                              ───────────────────
 *       CUDA app                          gpu-broker
 *           ↓                                 ↓
 *       nvidia-shim.ko ───vsock CID=3───► real nvidia.ko
 *           ↓                                 ↓
 *       /dev/nvidiactl (fake)             /dev/nvidiactl (real)
 *
 * Build:
 *   make                           # Guest mode (default)
 *   make NV_SHIM_HOST=1            # Host mode
 *
 * Usage (guest mode):
 *   insmod nvidia-shim.ko broker_cid=2 broker_port=9999
 *
 * Usage (host mode):
 *   insmod nvidia-shim.ko broker_cid=3 broker_port=9999
 *   (where CID=3 is the VM's CID)
 */

/*
 * Build mode selection:
 *   NV_SHIM_HOST=0 : Guest mode - connect to host (CID=2)
 *   NV_SHIM_HOST=1 : Host mode  - connect to guest VM (CID=guest)
 *
 * This affects:
 *   - Default CID (2 for guest→host, must specify for host→guest)
 *   - Module description
 *   - Debug messages
 */
#ifndef NV_SHIM_HOST
#define NV_SHIM_HOST 0
#endif

#include <linux/module.h>
#include <linux/kernel.h>
#include <linux/init.h>
#include <linux/fs.h>
#include <linux/cdev.h>
#include <linux/device.h>
#include <linux/uaccess.h>
#include <linux/slab.h>
#include <linux/poll.h>
#include <linux/mm.h>
#include <linux/wait.h>
#include <linux/sched.h>
#include <linux/atomic.h>
#include <linux/mutex.h>
#include <linux/kthread.h>
#include <linux/net.h>
#include <linux/socket.h>
#include <linux/vm_sockets.h>
#include <linux/un.h>
#include <net/net_namespace.h>

#define NV_SHIM_NAME        "nvidia-shim"
#define NV_SHIM_VERSION     "0.3.0"

#if NV_SHIM_HOST
#define NV_SHIM_MODE        "host"
#define NV_SHIM_DEFAULT_CID 3   /* Must be overridden with actual guest CID */
#else
#define NV_SHIM_MODE        "guest"
#define NV_SHIM_DEFAULT_CID 2   /* VMADDR_CID_HOST */
#endif

/* NVIDIA uses major 195 */
#define NV_MAJOR            195
#define NV_CTL_MINOR        255
#define NV_MAX_DEVICES      32

/* nvidia-uvm uses a dynamic major */
#define NV_UVM_NAME         "nvidia-uvm"

/* UVM ioctl codes (type=0x00, no magic) */
#define UVM_INITIALIZE      0x01
#define UVM_DEINITIALIZE    0x02
#define UVM_MM_INITIALIZE   0x4B

/* Maximum ioctl data size */
#define MAX_IOCTL_SIZE      4096

/* Timeout for broker responses (ms) */
#define RESPONSE_TIMEOUT_MS 5000

/* Wire protocol constants */
#define WIRE_MAGIC          0x4E56424B  /* "NVBK" */
#define WIRE_VERSION        1

/* Operation types - must match broker */
#define OP_REGISTER_CLIENT  0
#define OP_UNREGISTER       1
#define OP_ALLOC            2
#define OP_FREE             3
#define OP_CONTROL          4
#define OP_MAP_MEMORY       5
#define OP_UNMAP_MEMORY     6
#define OP_CARD_INFO        7
#define OP_CHECK_VERSION    8
#define OP_REGISTER_FD      9
#define OP_ALLOC_OS_EVENT   10
#define OP_FREE_OS_EVENT    11
#define OP_ATTACH_GPUS      12
#define OP_STATUS_CODE      13
#define OP_DUP_OBJECT       14
#define OP_SHARE            15
#define OP_SYS_PARAMS       16
#define OP_GET_PCI_INFO     17
#define OP_EXPORT_DEVICE_FD 18

/* NVIDIA escape code ranges */
/* Top-level escape codes (200+) */
#define NV_ESC_CARD_INFO         200
#define NV_ESC_REGISTER_FD       201
#define NV_ESC_ALLOC_OS_EVENT    206
#define NV_ESC_FREE_OS_EVENT     207
#define NV_ESC_STATUS_CODE       209
#define NV_ESC_CHECK_VERSION_STR 210
#define NV_ESC_ATTACH_GPUS_TO_FD 212
#define NV_ESC_SYS_PARAMS        214
#define NV_ESC_GET_PCI_INFO      215  /* Note: this is NUMA_INFO on nvidiactl but PCI_INFO on nvidia0 */
#define NV_ESC_EXPORT_DEVICE_FD  218

/* RM escape codes */
#define NV_ESC_RM_ALLOC_MEMORY   0x27
#define NV_ESC_RM_ALLOC_OBJECT   0x28
#define NV_ESC_RM_FREE           0x29
#define NV_ESC_RM_CONTROL        0x2A
#define NV_ESC_RM_ALLOC          0x2B
#define NV_ESC_RM_DUP_OBJECT     0x34
#define NV_ESC_RM_SHARE          0x35
#define NV_ESC_RM_MAP_MEMORY     0x4E
#define NV_ESC_RM_UNMAP_MEMORY   0x4F

/* NVIDIA ioctl magic */
#define NV_IOCTL_MAGIC      'F'

MODULE_LICENSE("GPL");
MODULE_AUTHOR("Isospin Authors");
#if NV_SHIM_HOST
MODULE_DESCRIPTION("NVIDIA GPU broker shim - HOST mode (forwards to GPU VM)");
#else
MODULE_DESCRIPTION("NVIDIA GPU broker shim - GUEST mode (forwards to host broker)");
#endif
MODULE_VERSION(NV_SHIM_VERSION);

/* --------------------------------------------------------------------------
 * Wire Protocol Structures
 * -------------------------------------------------------------------------- */

/*
 * Request header sent over vsock
 */
struct wire_request {
    u32 magic;
    u32 version;
    u64 client_id;
    u64 seq;
    u32 op_type;
    u32 payload_len;
    /* payload follows */
} __attribute__((packed));

/*
 * Response header received over vsock
 */
struct wire_response {
    u32 magic;
    u32 version;
    u64 client_id;
    u64 seq;
    u8  success;
    u8  _pad[3];
    u32 result_len;
    /* result follows */
} __attribute__((packed));

/* --------------------------------------------------------------------------
 * Data Structures
 * -------------------------------------------------------------------------- */

/*
 * Broker connection state
 */
struct nv_shim_broker {
    struct socket *sock;
    struct mutex lock;
    u64 client_id;
    atomic64_t next_seq;
    bool connected;
    
    /* Reconnection */
    struct task_struct *connect_thread;
    wait_queue_head_t connect_wq;
    bool should_stop;
};

/*
 * Per-open-file state
 */
struct nv_shim_file {
    struct nv_shim_broker *broker;
    int minor;
};

/*
 * Global driver state
 */
static struct {
    struct class *class;
    struct cdev cdev;
    dev_t devno;
    struct nv_shim_broker *broker;
} nv_shim;

/*
 * UVM device state (separate from main nvidia device)
 */
static struct {
    struct class *class;
    struct cdev cdev;
    dev_t devno;
    bool initialized;
} nv_uvm;

/* Module parameters */
static unsigned int broker_cid = NV_SHIM_DEFAULT_CID;
static unsigned int broker_port = 9999;
static char *broker_socket = NULL;  /* Unix socket path (for testing) */

module_param(broker_cid, uint, 0444);
#if NV_SHIM_HOST
MODULE_PARM_DESC(broker_cid, "Broker vsock CID (guest VM's CID, REQUIRED in host mode)");
#else
MODULE_PARM_DESC(broker_cid, "Broker vsock CID (default: 2 = host)");
#endif

module_param(broker_port, uint, 0444);
MODULE_PARM_DESC(broker_port, "Broker vsock port (default: 9999)");

module_param(broker_socket, charp, 0444);
MODULE_PARM_DESC(broker_socket, "Broker Unix socket path (for testing, overrides vsock)");

/* --------------------------------------------------------------------------
 * vsock Communication
 * -------------------------------------------------------------------------- */

/*
 * Connect to the broker over vsock or Unix socket
 */
static int
nv_shim_connect(struct nv_shim_broker *broker)
{
    int ret;
    
    if (broker->connected)
        return 0;
    
    mutex_lock(&broker->lock);
    
    if (broker->connected) {
        mutex_unlock(&broker->lock);
        return 0;
    }
    
    /* Check if Unix socket mode (host testing) or vsock mode (VM) */
    if (broker_socket && broker_socket[0]) {
        /* Unix socket mode - for host testing */
        struct sockaddr_un addr;
        
        ret = sock_create_kern(&init_net, AF_UNIX, SOCK_STREAM, 0, &broker->sock);
        if (ret < 0) {
            pr_err("nv-shim: failed to create unix socket: %d\n", ret);
            mutex_unlock(&broker->lock);
            return ret;
        }
        
        memset(&addr, 0, sizeof(addr));
        addr.sun_family = AF_UNIX;
        strncpy(addr.sun_path, broker_socket, sizeof(addr.sun_path) - 1);
        
        ret = kernel_connect(broker->sock, (struct sockaddr *)&addr,
                             sizeof(addr), 0);
        if (ret < 0) {
            pr_err("nv-shim: failed to connect to broker at %s: %d\n",
                   broker_socket, ret);
            sock_release(broker->sock);
            broker->sock = NULL;
            mutex_unlock(&broker->lock);
            return ret;
        }
        
        pr_info("nv-shim: connected to broker at unix:%s\n", broker_socket);
    } else {
        /* vsock mode - for VMs */
        struct sockaddr_vm addr;
        
        ret = sock_create_kern(&init_net, AF_VSOCK, SOCK_STREAM, 0, &broker->sock);
        if (ret < 0) {
            pr_err("nv-shim: failed to create vsock: %d\n", ret);
            mutex_unlock(&broker->lock);
            return ret;
        }
        
        memset(&addr, 0, sizeof(addr));
        addr.svm_family = AF_VSOCK;
        addr.svm_cid = broker_cid;
        addr.svm_port = broker_port;
        
        ret = kernel_connect(broker->sock, (struct sockaddr *)&addr,
                             sizeof(addr), 0);
        if (ret < 0) {
            pr_err("nv-shim: failed to connect to broker at %u:%u: %d\n",
                   broker_cid, broker_port, ret);
            sock_release(broker->sock);
            broker->sock = NULL;
            mutex_unlock(&broker->lock);
            return ret;
        }
        
        pr_info("nv-shim: connected to broker at cid=%u port=%u\n",
                broker_cid, broker_port);
    }
    
    broker->connected = true;
    mutex_unlock(&broker->lock);
    
    return 0;
}

/*
 * Disconnect from broker
 */
static void
nv_shim_disconnect(struct nv_shim_broker *broker)
{
    mutex_lock(&broker->lock);
    
    if (broker->sock) {
        kernel_sock_shutdown(broker->sock, SHUT_RDWR);
        sock_release(broker->sock);
        broker->sock = NULL;
    }
    broker->connected = false;
    
    mutex_unlock(&broker->lock);
}

/*
 * Send data over vsock
 */
static int
nv_shim_send(struct nv_shim_broker *broker, void *data, size_t len)
{
    struct kvec iov = { .iov_base = data, .iov_len = len };
    struct msghdr msg = { };
    int ret;
    
    if (!broker->connected || !broker->sock)
        return -ENOTCONN;
    
    ret = kernel_sendmsg(broker->sock, &msg, &iov, 1, len);
    if (ret < 0) {
        pr_err("nv-shim: send failed: %d\n", ret);
        return ret;
    }
    if (ret != len) {
        pr_err("nv-shim: short send: %d < %zu\n", ret, len);
        return -EIO;
    }
    
    return 0;
}

/*
 * Receive data over vsock
 */
static int
nv_shim_recv(struct nv_shim_broker *broker, void *buf, size_t len)
{
    struct kvec iov = { .iov_base = buf, .iov_len = len };
    struct msghdr msg = { };
    size_t received = 0;
    int ret;
    
    if (!broker->connected || !broker->sock)
        return -ENOTCONN;
    
    while (received < len) {
        iov.iov_base = buf + received;
        iov.iov_len = len - received;
        
        ret = kernel_recvmsg(broker->sock, &msg, &iov, 1,
                             len - received, 0);
        if (ret < 0) {
            pr_err("nv-shim: recv failed: %d\n", ret);
            return ret;
        }
        if (ret == 0) {
            pr_err("nv-shim: connection closed by broker\n");
            broker->connected = false;
            return -ECONNRESET;
        }
        received += ret;
    }
    
    return 0;
}

/*
 * Send a request and receive response
 */
static int
nv_shim_rpc(struct nv_shim_broker *broker,
            u32 op_type,
            void *payload, size_t payload_len,
            void *result, size_t result_size, size_t *result_len)
{
    struct wire_request *req;
    struct wire_response resp;
    size_t req_size;
    u64 seq;
    int ret;
    
    req_size = sizeof(*req) + payload_len;
    req = kzalloc(req_size, GFP_KERNEL);
    if (!req)
        return -ENOMEM;
    
    /* Build request */
    seq = atomic64_fetch_add(1, &broker->next_seq);
    req->magic = WIRE_MAGIC;
    req->version = WIRE_VERSION;
    req->client_id = broker->client_id;
    req->seq = seq;
    req->op_type = op_type;
    req->payload_len = payload_len;
    
    if (payload_len > 0 && payload)
        memcpy(req + 1, payload, payload_len);
    
    mutex_lock(&broker->lock);
    
    /* Send request */
    ret = nv_shim_send(broker, req, req_size);
    if (ret < 0)
        goto out;
    
    /* Receive response header */
    ret = nv_shim_recv(broker, &resp, sizeof(resp));
    if (ret < 0)
        goto out;
    
    /* Validate response */
    if (resp.magic != WIRE_MAGIC) {
        pr_err("nv-shim: bad response magic: 0x%x\n", resp.magic);
        ret = -EPROTO;
        goto out;
    }
    
    if (resp.seq != seq) {
        pr_err("nv-shim: seq mismatch: got %llu, expected %llu\n",
               resp.seq, seq);
        ret = -EPROTO;
        goto out;
    }
    
    /* Receive result payload */
    if (resp.result_len > 0) {
        if (resp.result_len > result_size) {
            pr_err("nv-shim: result too large: %u > %zu\n",
                   resp.result_len, result_size);
            ret = -ENOSPC;
            goto out;
        }
        
        ret = nv_shim_recv(broker, result, resp.result_len);
        if (ret < 0)
            goto out;
    }
    
    if (result_len)
        *result_len = resp.result_len;
    
    ret = resp.success ? 0 : -EIO;
    
out:
    mutex_unlock(&broker->lock);
    kfree(req);
    return ret;
}

/* --------------------------------------------------------------------------
 * ioctl Forwarding
 * -------------------------------------------------------------------------- */

/*
 * Determine operation type from escape code
 */
static u32
escape_to_op_type(u32 escape_code)
{
    switch (escape_code) {
    /* Top-level escapes (200+) */
    case NV_ESC_CARD_INFO:
        return OP_CARD_INFO;
    case NV_ESC_CHECK_VERSION_STR:
        return OP_CHECK_VERSION;
    case NV_ESC_REGISTER_FD:
        return OP_REGISTER_FD;
    case NV_ESC_ALLOC_OS_EVENT:
        return OP_ALLOC_OS_EVENT;
    case NV_ESC_FREE_OS_EVENT:
        return OP_FREE_OS_EVENT;
    case NV_ESC_ATTACH_GPUS_TO_FD:
        return OP_ATTACH_GPUS;
    case NV_ESC_STATUS_CODE:
        return OP_STATUS_CODE;
    case NV_ESC_SYS_PARAMS:
        return OP_SYS_PARAMS;
    case NV_ESC_GET_PCI_INFO:
        return OP_GET_PCI_INFO;
    case NV_ESC_EXPORT_DEVICE_FD:
        return OP_EXPORT_DEVICE_FD;
    
    /* RM escapes */
    case NV_ESC_RM_ALLOC:
    case NV_ESC_RM_ALLOC_MEMORY:
    case NV_ESC_RM_ALLOC_OBJECT:
        return OP_ALLOC;
    case NV_ESC_RM_FREE:
        return OP_FREE;
    case NV_ESC_RM_CONTROL:
        return OP_CONTROL;
    case NV_ESC_RM_DUP_OBJECT:
        return OP_DUP_OBJECT;
    case NV_ESC_RM_SHARE:
        return OP_SHARE;
    case NV_ESC_RM_MAP_MEMORY:
        return OP_MAP_MEMORY;
    case NV_ESC_RM_UNMAP_MEMORY:
        return OP_UNMAP_MEMORY;
    
    /* Everything else is a Control operation */
    default:
        return OP_CONTROL;
    }
}

/*
 * Build payload for specific operation types
 */
static int
build_payload(u32 op_type, u32 escape_code,
              void __user *arg, size_t arg_size,
              void *payload, size_t *payload_len)
{
    u8 *p = payload;
    
    switch (op_type) {
    case OP_CARD_INFO:
        /* No payload */
        *payload_len = 0;
        return 0;
        
    case OP_CHECK_VERSION:
        /* [cmd: u32] [reply: u32] [version_string...] */
        if (arg_size >= 8 && arg) {
            if (copy_from_user(p, arg, arg_size))
                return -EFAULT;
            *payload_len = arg_size;
        } else {
            *payload_len = 0;
        }
        return 0;
        
    case OP_ALLOC:
        /* [h_root: u32] [h_parent: u32] [h_object: u32] [class: u32] [params...] */
        if (arg_size > 0 && arg) {
            if (copy_from_user(p, arg, arg_size))
                return -EFAULT;
            *payload_len = arg_size;
        } else {
            *payload_len = 0;
        }
        return 0;
        
    case OP_FREE:
        /* [h_root: u32] [h_object: u32] */
        if (arg_size >= 8 && arg) {
            if (copy_from_user(p, arg, 8))
                return -EFAULT;
            *payload_len = 8;
        } else {
            *payload_len = 0;
        }
        return 0;
        
    case OP_CONTROL:
        /* [h_client: u32] [h_object: u32] [cmd: u32] [params_size: u32] [params...] */
        {
            u32 header[4];
            if (arg_size < 16) {
                *payload_len = 0;
                return 0;
            }
            if (copy_from_user(header, arg, 16))
                return -EFAULT;
            
            /* header[0] = hClient, header[1] = hObject, header[2] = cmd, header[3] = paramsSize */
            memcpy(p, header, 16);
            *payload_len = 16;
            
            /* Copy params if present */
            if (header[3] > 0 && arg_size > 24) {
                size_t params_size = min_t(size_t, header[3], arg_size - 24);
                if (copy_from_user(p + 16, (char __user *)arg + 24, params_size))
                    return -EFAULT;
                *payload_len += params_size;
            }
        }
        return 0;
        
    default:
        /* Generic: just copy raw params */
        if (arg_size > 0 && arg) {
            if (copy_from_user(p, arg, arg_size))
                return -EFAULT;
            *payload_len = arg_size;
        } else {
            *payload_len = 0;
        }
        return 0;
    }
}

/*
 * Parse broker result and copy appropriate data to userspace.
 * 
 * Broker result format: [result_type: u32] [type-specific data...]
 * 
 * This function extracts the correct portion for each ioctl type
 * and formats it as the NVIDIA userspace libraries expect.
 */
static int
copy_result_to_user(u32 op_type, void *result, size_t result_len,
                    void __user *arg, size_t arg_size)
{
    u8 *r = result;
    u32 result_type;
    
    if (result_len < 4)
        return 0;  /* Empty result is OK for some ops */
    
    result_type = le32_to_cpup((__le32 *)r);
    
    pr_debug("nv-shim: result_type=%u result_len=%zu arg_size=%zu\n",
             result_type, result_len, arg_size);
    
    switch (op_type) {
    case OP_CARD_INFO:
        /*
         * Broker returns: [7u32] [num_gpus: u32] [card_info...]
         * User expects: [card_info...] (array of NvCardInfo structs)
         * 
         * NvCardInfo is 80 bytes. First field 'valid' indicates if valid.
         * We need to copy starting from offset 8 (skip result_type + num_gpus)
         */
        if (result_len > 8) {
            size_t data_offset = 8;  /* Skip [result_type] [num_gpus] */
            size_t data_len = result_len - data_offset;
            size_t copy_len = min(data_len, arg_size);
            
            if (copy_to_user(arg, r + data_offset, copy_len))
                return -EFAULT;
        }
        break;
        
    case OP_CHECK_VERSION:
        /*
         * Broker returns: [8u32] [reply: u32] [version_string...]
         * User expects: [cmd: u32] [reply: u32] [version_string...]
         * 
         * We need to write back the reply field and version string
         * to the same buffer the user passed in.
         * 
         * User's input was: [cmd: u32] [reply: u32] [version_string...]
         * We update reply (offset 4) and version string (offset 8)
         */
        if (result_len >= 8 && arg_size >= 8) {
            /* Copy reply field (4 bytes at offset 4 in result) to user offset 4 */
            u32 reply = le32_to_cpup((__le32 *)(r + 4));
            if (copy_to_user((char __user *)arg + 4, &reply, 4))
                return -EFAULT;
            
            /* Copy version string if present */
            if (result_len > 8 && arg_size > 8) {
                size_t str_len = min(result_len - 8, arg_size - 8);
                if (copy_to_user((char __user *)arg + 8, r + 8, str_len))
                    return -EFAULT;
            }
        }
        break;
        
    case OP_ALLOC:
        /*
         * Broker returns: [2u32] [status: u32] [real_handle: u32]
         * User expects: Same struct as input with status field updated
         * 
         * For NV_ESC_RM_ALLOC, the status is at a specific offset in the struct.
         * We just need to copy back the status (0 = success).
         */
        if (result_len >= 12 && arg_size >= 4) {
            u32 status = le32_to_cpup((__le32 *)(r + 4));
            /* Status field is at the end of the NVOS21_PARAMETERS struct */
            /* For simplicity, we just leave the user's data unchanged and return 0 on success */
            if (status != 0) {
                pr_warn("nv-shim: alloc failed with status %u\n", status);
                return -EIO;
            }
        }
        break;
        
    case OP_FREE:
        /*
         * Broker returns: [3u32] [status: u32] [real_handle: u32]
         * User expects: Same struct as input with status updated
         */
        if (result_len >= 8) {
            u32 status = le32_to_cpup((__le32 *)(r + 4));
            if (status != 0) {
                pr_warn("nv-shim: free failed with status %u\n", status);
                return -EIO;
            }
        }
        break;
        
    case OP_CONTROL:
        /*
         * Broker returns: [4u32] [status: u32] [out_params...]
         * User expects: Same struct as input with params updated
         * 
         * We need to copy status and out_params back to user's buffer
         */
        if (result_len >= 8 && arg_size >= 4) {
            u32 status = le32_to_cpup((__le32 *)(r + 4));
            /* Copy status to user - exact offset depends on struct layout */
            /* For NVOS54_PARAMETERS: status is at offset 20 */
            if (arg_size >= 24) {
                if (copy_to_user((char __user *)arg + 20, &status, 4))
                    return -EFAULT;
            }
            
            /* 
             * Note: out_params copy not yet implemented.
             * The params format is complex (pointer at offset 24 in struct,
             * but data may be inline for small params).
             * For M1 (nvidia-smi -L), we don't need out_params.
             */
            (void)result_len;  /* Suppress unused warning */
        }
        break;
        
    case OP_SYS_PARAMS:
        /*
         * Broker returns: [16u32] [memblock_size: u64]
         * User expects: [memblock_size: u64] (8 bytes)
         */
        if (result_len >= 12 && arg_size >= 8) {
            if (copy_to_user(arg, r + 4, 8))
                return -EFAULT;
        }
        break;
        
    case OP_GET_PCI_INFO:
        /*
         * Broker returns: [17u32] [pci_info: 0x230 bytes]
         * User expects: [pci_info: 0x230 bytes]
         */
        if (result_len > 4) {
            size_t data_len = result_len - 4;
            size_t copy_len = min(data_len, arg_size);
            if (copy_to_user(arg, r + 4, copy_len))
                return -EFAULT;
        }
        break;
        
    case OP_EXPORT_DEVICE_FD:
        /*
         * Broker returns: [18u32] [status: u32]
         * User expects: [status: u32] (or similar small struct)
         */
        if (result_len >= 8 && arg_size >= 4) {
            u32 status = le32_to_cpup((__le32 *)(r + 4));
            if (copy_to_user(arg, &status, 4))
                return -EFAULT;
        }
        break;
        
    case OP_ATTACH_GPUS:
        /*
         * Broker returns: [12u32] (just success indicator)
         * User expects: No data modification needed
         */
        break;
        
    case OP_REGISTER_FD:
        /*
         * Broker returns: [9u32]
         * User expects: No data modification needed
         */
        break;
        
    case OP_STATUS_CODE:
        /*
         * Broker returns: [13u32] [status: u32]
         * User expects: [status: u32]
         */
        if (result_len >= 8 && arg_size >= 4) {
            u32 status = le32_to_cpup((__le32 *)(r + 4));
            if (copy_to_user(arg, &status, 4))
                return -EFAULT;
        }
        break;
        
    case OP_ALLOC_OS_EVENT:
    case OP_FREE_OS_EVENT:
        /*
         * Broker returns: [10u32/11u32] [status: u32]
         * User expects: Status field in struct updated
         */
        if (result_len >= 8 && arg_size >= 4) {
            u32 status = le32_to_cpup((__le32 *)(r + 4));
            /* Write status to appropriate offset in user struct */
            if (copy_to_user(arg, &status, 4))
                return -EFAULT;
        }
        break;
        
    default:
        /* Unknown op, try raw copy */
        if (result_len > 4) {
            size_t copy_len = min(result_len - 4, arg_size);
            if (copy_to_user(arg, r + 4, copy_len))
                return -EFAULT;
        }
        break;
    }
    
    return 0;
}

/*
 * Forward an ioctl to the broker
 */
static int
nv_shim_forward_ioctl(struct nv_shim_broker *broker,
                      unsigned int cmd,
                      void __user *arg,
                      size_t arg_size)
{
    void *payload = NULL;
    void *result = NULL;
    size_t payload_len, result_len;
    u32 escape_code, op_type;
    int ret;
    
    /* Extract escape code from ioctl command */
    escape_code = _IOC_NR(cmd);
    op_type = escape_to_op_type(escape_code);
    
    pr_debug("nv-shim: ioctl escape=0x%x op=%u size=%zu\n",
             escape_code, op_type, arg_size);
    
    /* Allocate buffers */
    payload = kzalloc(MAX_IOCTL_SIZE, GFP_KERNEL);
    result = kzalloc(MAX_IOCTL_SIZE, GFP_KERNEL);
    if (!payload || !result) {
        ret = -ENOMEM;
        goto out;
    }
    
    /* Build payload */
    ret = build_payload(op_type, escape_code, arg, arg_size,
                        payload, &payload_len);
    if (ret < 0)
        goto out;
    
    /* Ensure connected */
    ret = nv_shim_connect(broker);
    if (ret < 0)
        goto out;
    
    /* Send RPC */
    ret = nv_shim_rpc(broker, op_type,
                      payload, payload_len,
                      result, MAX_IOCTL_SIZE, &result_len);
    if (ret < 0)
        goto out;
    
    /* Parse result and copy appropriate data to user */
    ret = copy_result_to_user(op_type, result, result_len, arg, arg_size);
    
out:
    kfree(payload);
    kfree(result);
    return ret;
}

/* --------------------------------------------------------------------------
 * File Operations
 * -------------------------------------------------------------------------- */

static int
nvidia_shim_open(struct inode *inode, struct file *file)
{
    struct nv_shim_file *nvf;
    int minor = iminor(inode);
    
    pr_debug("nv-shim: open minor=%d\n", minor);
    
    nvf = kzalloc(sizeof(*nvf), GFP_KERNEL);
    if (!nvf)
        return -ENOMEM;
    
    nvf->broker = nv_shim.broker;
    nvf->minor = minor;
    
    file->private_data = nvf;
    
    return 0;
}

static int
nvidia_shim_release(struct inode *inode, struct file *file)
{
    struct nv_shim_file *nvf = file->private_data;
    
    pr_debug("nv-shim: release minor=%d\n", nvf->minor);
    
    kfree(nvf);
    file->private_data = NULL;
    
    return 0;
}

static long
nvidia_shim_unlocked_ioctl(struct file *file,
                           unsigned int cmd,
                           unsigned long arg)
{
    struct nv_shim_file *nvf = file->private_data;
    size_t arg_size = _IOC_SIZE(cmd);
    u8 magic = _IOC_TYPE(cmd);
    
    /* Only handle NVIDIA ioctls */
    if (magic != NV_IOCTL_MAGIC) {
        pr_debug("nv-shim: ignoring non-nvidia ioctl magic=0x%x\n", magic);
        return -ENOTTY;
    }
    
    if (!nvf || !nvf->broker) {
        pr_err("nv-shim: ioctl on invalid file\n");
        return -EINVAL;
    }
    
    return nv_shim_forward_ioctl(nvf->broker, cmd,
                                 (void __user *)arg, arg_size);
}

static int
nvidia_shim_mmap(struct file *file, struct vm_area_struct *vma)
{
    pr_debug("nv-shim: mmap offset=0x%lx size=0x%lx\n",
             vma->vm_pgoff << PAGE_SHIFT,
             vma->vm_end - vma->vm_start);
    
    /*
     * GPU memory mapping requires coordination with broker.
     * For now, return error - data path would use different mechanism.
     */
    pr_warn("nv-shim: mmap not implemented (control path only)\n");
    return -ENOSYS;
}

static struct file_operations nvidia_shim_fops = {
    .owner          = THIS_MODULE,
    .open           = nvidia_shim_open,
    .release        = nvidia_shim_release,
    .unlocked_ioctl = nvidia_shim_unlocked_ioctl,
#ifdef CONFIG_COMPAT
    .compat_ioctl   = nvidia_shim_unlocked_ioctl,
#endif
    .mmap           = nvidia_shim_mmap,
};

/* --------------------------------------------------------------------------
 * UVM Device Operations (stub for nvidia-uvm)
 * -------------------------------------------------------------------------- */

static int
nvidia_uvm_open(struct inode *inode, struct file *file)
{
    pr_debug("nv-uvm: open\n");
    return 0;
}

static int
nvidia_uvm_release(struct inode *inode, struct file *file)
{
    pr_debug("nv-uvm: release\n");
    return 0;
}

static long
nvidia_uvm_unlocked_ioctl(struct file *file, unsigned int cmd, unsigned long arg)
{
    u32 ioctl_nr = _IOC_NR(cmd);
    size_t arg_size = _IOC_SIZE(cmd);
    
    pr_debug("nv-uvm: ioctl nr=0x%x size=%zu\n", ioctl_nr, arg_size);
    
    /*
     * UVM ioctls are stubbed - we just return success.
     * The real nvidia-uvm driver manages unified virtual memory, but
     * for the broker model, memory management happens differently.
     */
    switch (ioctl_nr) {
    case UVM_INITIALIZE:
        pr_debug("nv-uvm: UVM_INITIALIZE\n");
        /* Zero out the large param buffer to indicate success */
        if (arg && arg_size > 0) {
            if (clear_user((void __user *)arg, min_t(size_t, arg_size, 4096)))
                return -EFAULT;
        }
        return 0;
        
    case UVM_DEINITIALIZE:
        pr_debug("nv-uvm: UVM_DEINITIALIZE\n");
        return 0;
        
    case UVM_MM_INITIALIZE:
        pr_debug("nv-uvm: UVM_MM_INITIALIZE\n");
        return 0;
        
    default:
        pr_debug("nv-uvm: unknown ioctl 0x%x\n", ioctl_nr);
        /* Return success for unknown ioctls - nvidia-smi may probe capabilities */
        return 0;
    }
}

static struct file_operations nvidia_uvm_fops = {
    .owner          = THIS_MODULE,
    .open           = nvidia_uvm_open,
    .release        = nvidia_uvm_release,
    .unlocked_ioctl = nvidia_uvm_unlocked_ioctl,
#ifdef CONFIG_COMPAT
    .compat_ioctl   = nvidia_uvm_unlocked_ioctl,
#endif
    .mmap           = nvidia_shim_mmap,
};

/* --------------------------------------------------------------------------
 * Module Init/Exit
 * -------------------------------------------------------------------------- */

static int
nv_shim_create_broker(void)
{
    struct nv_shim_broker *broker;
    
    broker = kzalloc(sizeof(*broker), GFP_KERNEL);
    if (!broker)
        return -ENOMEM;
    
    mutex_init(&broker->lock);
    atomic64_set(&broker->next_seq, 1);
    broker->client_id = 1;  /* Will be assigned by broker on connect */
    broker->connected = false;
    broker->sock = NULL;
    
    nv_shim.broker = broker;
    
    /* Try initial connection (non-fatal if fails) */
    if (nv_shim_connect(broker) < 0) {
        pr_warn("nv-shim: initial connection failed, will retry on first ioctl\n");
    }
    
    return 0;
}

static void
nv_shim_destroy_broker(void)
{
    struct nv_shim_broker *broker = nv_shim.broker;
    
    if (!broker)
        return;
    
    nv_shim_disconnect(broker);
    mutex_destroy(&broker->lock);
    kfree(broker);
    nv_shim.broker = NULL;
}

static int __init
nvidia_shim_init(void)
{
    int ret;
    
    pr_info("nv-shim: " NV_SHIM_NAME " v" NV_SHIM_VERSION " loading (" NV_SHIM_MODE " mode)\n");
    if (broker_socket && broker_socket[0]) {
        pr_info("nv-shim: broker_socket=%s (unix socket)\n", broker_socket);
    } else {
        pr_info("nv-shim: broker_cid=%u broker_port=%u (vsock)\n", broker_cid, broker_port);
#if NV_SHIM_HOST
        pr_info("nv-shim: HOST mode - forwarding to GPU VM at CID %u\n", broker_cid);
#else
        pr_info("nv-shim: GUEST mode - forwarding to host broker\n");
#endif
    }
    
    /* Allocate device numbers (major 195, minors 0-255)
     * We need all 256 minors because nvidiactl is minor 255 */
    nv_shim.devno = MKDEV(NV_MAJOR, 0);
    ret = register_chrdev_region(nv_shim.devno, 256, NV_SHIM_NAME);
    if (ret < 0) {
        pr_err("nv-shim: failed to register chrdev region: %d\n", ret);
        pr_err("nv-shim: (is another nvidia driver loaded?)\n");
        return ret;
    }
    
    /* Initialize cdev */
    cdev_init(&nv_shim.cdev, &nvidia_shim_fops);
    nv_shim.cdev.owner = THIS_MODULE;
    
    /* Register for all 256 minors to cover nvidia0-31 and nvidiactl (255) */
    ret = cdev_add(&nv_shim.cdev, nv_shim.devno, 256);
    if (ret < 0) {
        pr_err("nv-shim: failed to add cdev: %d\n", ret);
        goto err_unregister;
    }
    
    /* Create device class */
    nv_shim.class = class_create(NV_SHIM_NAME);
    if (IS_ERR(nv_shim.class)) {
        ret = PTR_ERR(nv_shim.class);
        pr_err("nv-shim: failed to create class: %d\n", ret);
        goto err_cdev;
    }
    
    /* Create device nodes */
    device_create(nv_shim.class, NULL, MKDEV(NV_MAJOR, NV_CTL_MINOR),
                  NULL, "nvidiactl");
    device_create(nv_shim.class, NULL, MKDEV(NV_MAJOR, 0),
                  NULL, "nvidia0");
    
    /* Create broker connection */
    ret = nv_shim_create_broker();
    if (ret < 0) {
        pr_err("nv-shim: failed to create broker: %d\n", ret);
        goto err_devices;
    }
    
    /* Create nvidia-uvm device (uses dynamic major) */
    ret = alloc_chrdev_region(&nv_uvm.devno, 0, 1, NV_UVM_NAME);
    if (ret < 0) {
        pr_warn("nv-shim: failed to register nvidia-uvm: %d (continuing without UVM)\n", ret);
        nv_uvm.initialized = false;
    } else {
        cdev_init(&nv_uvm.cdev, &nvidia_uvm_fops);
        nv_uvm.cdev.owner = THIS_MODULE;
        
        ret = cdev_add(&nv_uvm.cdev, nv_uvm.devno, 1);
        if (ret < 0) {
            pr_warn("nv-shim: failed to add nvidia-uvm cdev: %d\n", ret);
            unregister_chrdev_region(nv_uvm.devno, 1);
            nv_uvm.initialized = false;
        } else {
            nv_uvm.class = class_create(NV_UVM_NAME);
            if (IS_ERR(nv_uvm.class)) {
                pr_warn("nv-shim: failed to create nvidia-uvm class\n");
                cdev_del(&nv_uvm.cdev);
                unregister_chrdev_region(nv_uvm.devno, 1);
                nv_uvm.initialized = false;
            } else {
                device_create(nv_uvm.class, NULL, nv_uvm.devno, NULL, "nvidia-uvm");
                nv_uvm.initialized = true;
                pr_info("nv-shim: created /dev/nvidia-uvm\n");
            }
        }
    }
    
    pr_info("nv-shim: loaded successfully\n");
    pr_info("nv-shim: created /dev/nvidiactl and /dev/nvidia0\n");
    return 0;

err_devices:
    device_destroy(nv_shim.class, MKDEV(NV_MAJOR, 0));
    device_destroy(nv_shim.class, MKDEV(NV_MAJOR, NV_CTL_MINOR));
    class_destroy(nv_shim.class);
err_cdev:
    cdev_del(&nv_shim.cdev);
err_unregister:
    unregister_chrdev_region(nv_shim.devno, 256);
    return ret;
}

static void __exit
nvidia_shim_exit(void)
{
    pr_info("nv-shim: unloading\n");
    
    nv_shim_destroy_broker();
    
    /* Clean up nvidia-uvm if it was created */
    if (nv_uvm.initialized) {
        device_destroy(nv_uvm.class, nv_uvm.devno);
        class_destroy(nv_uvm.class);
        cdev_del(&nv_uvm.cdev);
        unregister_chrdev_region(nv_uvm.devno, 1);
    }
    
    device_destroy(nv_shim.class, MKDEV(NV_MAJOR, 0));
    device_destroy(nv_shim.class, MKDEV(NV_MAJOR, NV_CTL_MINOR));
    class_destroy(nv_shim.class);
    cdev_del(&nv_shim.cdev);
    unregister_chrdev_region(nv_shim.devno, 256);
    
    pr_info("nv-shim: unloaded\n");
}

module_init(nvidia_shim_init);
module_exit(nvidia_shim_exit);
