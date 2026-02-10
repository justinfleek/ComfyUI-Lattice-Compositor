# nix/flake-modules/vm-runners.nix
#
# GPU Broker Demo Stack - Runnable applications for demonstrating GPU multiplexing
#
# ════════════════════════════════════════════════════════════════════════════════
# Architecture Overview
# ════════════════════════════════════════════════════════════════════════════════
#
#   ┌──────────────────────────────────────────────────────────────────────────┐
#   │ GPU VM (Cloud Hypervisor + VFIO)                                         │
#   │   nvidia.ko (real driver) → RTX PRO 6000                                 │
#   │   gpu-broker (real ioctl forwarding) on vsock:9999                       │
#   └────────────────────────────────┬─────────────────────────────────────────┘
#                                    │ CH vsock
#                                    ▼
#   ┌──────────────────────────────────────────────────────────────────────────┐
#   │ HOST: vsock-bridge (Python)                                              │
#   │   Bridges Cloud Hypervisor vsock ↔ Firecracker vsock                     │
#   └────────────────────────────────┬─────────────────────────────────────────┘
#                                    │ FC vsock
#                                    ▼
#   ┌──────────────────────────────────────────────────────────────────────────┐
#   │ Worker VM (Firecracker)                                                  │
#   │   nvidia-shim.ko → /dev/nvidiactl, /dev/nvidia0 (proxied)               │
#   │   Applications use GPU without cold boot penalty                         │
#   └──────────────────────────────────────────────────────────────────────────┘
#
# ════════════════════════════════════════════════════════════════════════════════
# Quick Start
# ════════════════════════════════════════════════════════════════════════════════
#
#   # Full stack (requires GPU bound to vfio-pci, run as root):
#   sudo nix run .#demo-broker
#
#   # Manual step-by-step (3 terminals):
#   sudo nix run .#gpu-vm           # Terminal 1: GPU VM with broker
#   sudo nix run .#vsock-bridge     # Terminal 2: vsock proxy
#   sudo nix run .#worker-vm        # Terminal 3: Worker VM
#
#   # Cleanup:
#   sudo nix run .#kill-vms
#
# ════════════════════════════════════════════════════════════════════════════════
{ inputs, ... }:
{
  _class = "flake";

  config.perSystem =
    {
      pkgs,
      lib,
      config,
      ...
    }:
    let
      # ════════════════════════════════════════════════════════════════════════
      # Configuration
      # ════════════════════════════════════════════════════════════════════════

      cfg = {
        # Default GPU PCI address (override with GPU_PCI_ADDR env var)
        gpuPciAddr = "0000:01:00.0";

        # vsock configuration
        gpuVmCid = 3;
        workerVmCid = 5;
        brokerPort = 9999;

        # Socket paths
        gpuVmVsockSock = "/tmp/gpu-vm-vsock.sock";
        fcWorkerSock = "/tmp/fc-worker.sock";
        gpuVmLog = "/tmp/gpu-vm.log";

        # Asset paths (for kernel 6.12.63 + NVIDIA 580.95.05)
        # These are manual assets until gpu-vm-rootfs is fully Nix-ified
        projectDir = "/home/b7r6/src/vendor/isospin";
      };

      # Packages from other modules
      fcGpuKernel = config.packages.fc-gpu-kernel;
      fcRootfs = config.packages.fc-rootfs;

      # ════════════════════════════════════════════════════════════════════════
      # Helper: Check if GPU VM assets exist
      # ════════════════════════════════════════════════════════════════════════
      checkAssets = ''
        GPU_KERNEL="${cfg.projectDir}/.vm-assets/vmlinux-6.12.63.bin"
        GPU_INITRAMFS="${cfg.projectDir}/.vm-assets/initramfs-6.12.63-pci.cpio.gz"
        GPU_ROOTFS="${cfg.projectDir}/.vm-assets/gpu-rootfs.ext4"

        missing=""
        [ ! -f "$GPU_KERNEL" ] && missing="$missing\n  - $GPU_KERNEL"
        [ ! -f "$GPU_INITRAMFS" ] && missing="$missing\n  - $GPU_INITRAMFS"
        [ ! -f "$GPU_ROOTFS" ] && missing="$missing\n  - $GPU_ROOTFS"

        if [ -n "$missing" ]; then
          echo "ERROR: Missing GPU VM assets:$missing"
          echo ""
          echo "These assets contain the NVIDIA driver (580.95.05) for kernel 6.12.63."
          echo "See docs/session-state-*.md for how to create them."
          exit 1
        fi
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 1. gpu-vm: Boot GPU VM with real NVIDIA driver
      # ════════════════════════════════════════════════════════════════════════
      gpu-vm = pkgs.writeShellScriptBin "gpu-vm" ''
        set -euo pipefail

        echo "════════════════════════════════════════════════════════════════"
        echo "  GPU VM - Cloud Hypervisor + VFIO GPU + NVIDIA Driver + Broker"
        echo "════════════════════════════════════════════════════════════════"
        echo ""

        GPU_PCI_ADDR="''${GPU_PCI_ADDR:-${cfg.gpuPciAddr}}"

        # Check assets
        ${checkAssets}

        # Check VFIO binding
        if [ ! -d "/sys/bus/pci/devices/$GPU_PCI_ADDR/driver" ]; then
          echo "ERROR: GPU $GPU_PCI_ADDR not found"
          exit 1
        fi

        driver=$(basename $(readlink "/sys/bus/pci/devices/$GPU_PCI_ADDR/driver" 2>/dev/null) 2>/dev/null || echo "none")
        if [ "$driver" != "vfio-pci" ]; then
          echo "ERROR: GPU $GPU_PCI_ADDR bound to '$driver', not 'vfio-pci'"
          echo ""
          echo "Bind the GPU to vfio-pci first:"
          echo "  sudo ${cfg.projectDir}/scripts/vfio-bind.sh $GPU_PCI_ADDR"
          exit 1
        fi

        echo "  GPU:       $GPU_PCI_ADDR (vfio-pci)"
        echo "  Kernel:    $GPU_KERNEL"
        echo "  Initramfs: $GPU_INITRAMFS"
        echo "  Rootfs:    $GPU_ROOTFS"
        echo "  CID:       ${toString cfg.gpuVmCid}"
        echo "  Log:       ${cfg.gpuVmLog}"
        echo ""
        echo "Starting GPU VM (NVIDIA driver takes ~20s to load)..."
        echo "Press Ctrl+C to stop."
        echo ""

        rm -f "${cfg.gpuVmVsockSock}" "${cfg.gpuVmLog}" 2>/dev/null || true

        exec ${pkgs.cloud-hypervisor}/bin/cloud-hypervisor \
          --kernel "$GPU_KERNEL" \
          --initramfs "$GPU_INITRAMFS" \
          --disk path="$GPU_ROOTFS" \
          --cmdline "console=ttyS0 root=/dev/vda rw init=/init" \
          --cpus boot=2 --memory size=8G \
          --vsock cid=${toString cfg.gpuVmCid},socket="${cfg.gpuVmVsockSock}" \
          --device path=/sys/bus/pci/devices/$GPU_PCI_ADDR \
          --serial file="${cfg.gpuVmLog}" --console off
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 2. vsock-bridge: Bridge FC ↔ CH vsock domains
      # ════════════════════════════════════════════════════════════════════════
      vsock-bridge = pkgs.writeShellScriptBin "vsock-bridge" ''
                set -euo pipefail
                
                echo "════════════════════════════════════════════════════════════════"
                echo "  Vsock Bridge - Firecracker ↔ Cloud Hypervisor"
                echo "════════════════════════════════════════════════════════════════"
                echo ""
                
                if [ ! -S "${cfg.gpuVmVsockSock}" ]; then
                  echo "ERROR: GPU VM vsock socket not found at ${cfg.gpuVmVsockSock}"
                  echo ""
                  echo "Start the GPU VM first:"
                  echo "  sudo nix run .#gpu-vm"
                  exit 1
                fi
                
                echo "  FC socket: ${cfg.fcWorkerSock}_${toString cfg.brokerPort}"
                echo "  CH socket: ${cfg.gpuVmVsockSock}"
                echo "  Port:      ${toString cfg.brokerPort}"
                echo ""
                echo "Bridge running. Press Ctrl+C to stop."
                echo ""
                
                exec ${pkgs.python3}/bin/python3 << 'PYTHON'
        import socket, os, sys, threading

        FC_SOCK = "${cfg.fcWorkerSock}_${toString cfg.brokerPort}"
        CH_SOCK = "${cfg.gpuVmVsockSock}"
        CH_PORT = ${toString cfg.brokerPort}

        def proxy(src, dst):
            try:
                while True:
                    data = src.recv(65536)
                    if not data: break
                    dst.sendall(data)
            except: pass
            finally:
                try: src.close()
                except: pass
                try: dst.close()
                except: pass

        def handle(fc, n):
            try:
                ch = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                ch.connect(CH_SOCK)
                ch.sendall(f"CONNECT {CH_PORT}\n".encode())
                resp = ch.recv(1024)
                if not resp.startswith(b"OK"):
                    print(f"[{n}] CH connect failed: {resp}")
                    fc.close(); ch.close(); return
                print(f"[{n}] Bridge established")
                t1 = threading.Thread(target=proxy, args=(fc, ch))
                t2 = threading.Thread(target=proxy, args=(ch, fc))
                t1.start(); t2.start(); t1.join(); t2.join()
                print(f"[{n}] Disconnected")
            except Exception as e:
                print(f"[{n}] Error: {e}")

        try: os.unlink(FC_SOCK)
        except: pass

        srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        srv.bind(FC_SOCK)
        os.chmod(FC_SOCK, 0o777)
        srv.listen(100)
        print(f"Listening on {FC_SOCK}")

        n = 0
        while True:
            conn, _ = srv.accept()
            n += 1
            print(f"[{n}] New connection")
            threading.Thread(target=handle, args=(conn, n), daemon=True).start()
        PYTHON
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 3. worker-vm: Boot worker VM with nvidia-shim
      # ════════════════════════════════════════════════════════════════════════
      worker-vm = pkgs.writeShellScriptBin "worker-vm" ''
                set -euo pipefail
                
                echo "════════════════════════════════════════════════════════════════"
                echo "  Worker VM - Firecracker + nvidia-shim"
                echo "════════════════════════════════════════════════════════════════"
                echo ""
                
                KERNEL="${fcGpuKernel}/vmlinux"
                ROOTFS_SRC="${fcRootfs}/rootfs.ext4"
                ROOTFS="/tmp/fc-worker-rootfs.ext4"
                
                bridge_sock="${cfg.fcWorkerSock}_${toString cfg.brokerPort}"
                if [ ! -S "$bridge_sock" ]; then
                  echo "WARNING: Vsock bridge not found at $bridge_sock"
                  echo "         Worker VM will boot but cannot connect to GPU broker."
                  echo ""
                  echo "Start the bridge first:"
                  echo "  sudo nix run .#vsock-bridge"
                  echo ""
                fi
                
                echo "  Kernel:  $KERNEL"
                echo "  Rootfs:  $ROOTFS_SRC"
                echo "  CID:     ${toString cfg.workerVmCid}"
                echo ""
                
                cp "$ROOTFS_SRC" "$ROOTFS"
                chmod 644 "$ROOTFS"
                rm -f "${cfg.fcWorkerSock}" 2>/dev/null || true
                
                cat > /tmp/fc-worker.json << EOF
        {
          "boot-source": {
            "kernel_image_path": "$KERNEL",
            "boot_args": "console=ttyS0 reboot=k panic=1 pci=off"
          },
          "drives": [{"drive_id": "rootfs", "path_on_host": "$ROOTFS", "is_root_device": true, "is_read_only": false}],
          "machine-config": {"vcpu_count": 1, "mem_size_mib": 512},
          "vsock": {"guest_cid": ${toString cfg.workerVmCid}, "uds_path": "${cfg.fcWorkerSock}"}
        }
        EOF
                
                echo "Starting worker VM..."
                echo ""
                exec ${pkgs.firecracker}/bin/firecracker --no-api --config-file /tmp/fc-worker.json
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 4. kill-vms: Stop all VMs and cleanup
      # ════════════════════════════════════════════════════════════════════════
      kill-vms = pkgs.writeShellScriptBin "kill-vms" ''
        echo "Stopping GPU broker stack..."
        pkill -9 cloud-hyperviso 2>/dev/null && echo "  Killed cloud-hypervisor" || true
        pkill -9 firecracker 2>/dev/null && echo "  Killed firecracker" || true
        pkill -f "vsock-bridge\|vsock_bridge" 2>/dev/null && echo "  Killed vsock-bridge" || true
        rm -f "${cfg.gpuVmVsockSock}" "${cfg.fcWorkerSock}" "${cfg.fcWorkerSock}_"* /tmp/fc-worker.json 2>/dev/null || true
        echo "Done."
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 5. demo-broker: Full stack demo with tmux
      # ════════════════════════════════════════════════════════════════════════
      demo-broker = pkgs.writeShellScriptBin "demo-broker" ''
        set -euo pipefail

        echo "════════════════════════════════════════════════════════════════"
        echo "  Isospin GPU Broker Demo"
        echo "════════════════════════════════════════════════════════════════"
        echo ""
        echo "This demo shows GPU multiplexing without cold boot penalty:"
        echo ""
        echo "  1. GPU VM boots with real NVIDIA driver (~20s)"
        echo "  2. gpu-broker serves ioctls via vsock"
        echo "  3. Worker VMs connect instantly via nvidia-shim"
        echo ""

        # Check prerequisites
        ${checkAssets}

        GPU_PCI_ADDR="''${GPU_PCI_ADDR:-${cfg.gpuPciAddr}}"
        driver=$(basename $(readlink "/sys/bus/pci/devices/$GPU_PCI_ADDR/driver" 2>/dev/null) 2>/dev/null || echo "none")
        if [ "$driver" != "vfio-pci" ]; then
          echo "ERROR: GPU not bound to vfio-pci"
          echo "  Run: sudo ${cfg.projectDir}/scripts/vfio-bind.sh $GPU_PCI_ADDR"
          exit 1
        fi

        # Cleanup
        ${kill-vms}/bin/kill-vms 2>/dev/null || true
        sleep 1

        SESSION="isospin-demo"
        ${pkgs.tmux}/bin/tmux kill-session -t $SESSION 2>/dev/null || true

        echo "Starting tmux session '$SESSION'..."
        echo ""

        # Window 0: GPU VM
        ${pkgs.tmux}/bin/tmux new-session -d -s $SESSION -n "gpu-vm" "${gpu-vm}/bin/gpu-vm"

        # Wait for GPU VM vsock
        echo -n "Waiting for GPU VM vsock..."
        for i in $(seq 1 30); do
          [ -S "${cfg.gpuVmVsockSock}" ] && break
          sleep 1
          echo -n "."
        done
        echo ""

        if [ ! -S "${cfg.gpuVmVsockSock}" ]; then
          echo "ERROR: GPU VM failed to create vsock socket"
          ${pkgs.tmux}/bin/tmux kill-session -t $SESSION 2>/dev/null || true
          exit 1
        fi

        # Window 1: Bridge
        ${pkgs.tmux}/bin/tmux new-window -t $SESSION -n "bridge" "${vsock-bridge}/bin/vsock-bridge"
        sleep 2

        # Window 2: Worker VM
        ${pkgs.tmux}/bin/tmux new-window -t $SESSION -n "worker" "${worker-vm}/bin/worker-vm"

        # Window 3: GPU VM log
        ${pkgs.tmux}/bin/tmux new-window -t $SESSION -n "log" "tail -f ${cfg.gpuVmLog}"

        ${pkgs.tmux}/bin/tmux select-window -t $SESSION:worker

        echo ""
        echo "Demo running in tmux session '$SESSION'"
        echo ""
        echo "  Windows:"
        echo "    0: gpu-vm  - GPU VM (watch NVIDIA driver load)"
        echo "    1: bridge  - Vsock bridge (shows connections)"
        echo "    2: worker  - Worker VM (nvidia-shim loaded)"
        echo "    3: log     - GPU VM serial log"
        echo ""
        echo "  Commands:"
        echo "    Attach:   tmux attach -t $SESSION"
        echo "    Kill:     nix run .#kill-vms"
        echo ""

        exec ${pkgs.tmux}/bin/tmux attach -t $SESSION
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 6. broker-test: Run gpu-broker unit tests
      # ════════════════════════════════════════════════════════════════════════
      broker-test = pkgs.writeShellScriptBin "broker-test" ''
        set -euo pipefail
        cd ${cfg.projectDir}/gpu-broker
        echo "Running gpu-broker tests..."
        exec ${pkgs.cargo}/bin/cargo test "$@"
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 7. gpu-run: Run commands in NGC containers with GPU passthrough
      # ════════════════════════════════════════════════════════════════════════
      #
      # Usage:
      #   nix run .#gpu-run -- /bin/bash nvcr.io/nvidia/tritonserver:25.11-py3
      #   nix run .#gpu-run -- python -c "import torch; print(torch.cuda.is_available())" nvcr.io/nvidia/pytorch:25.04-py3
      #
      # This uses bubblewrap (bwrap) to create an isolated namespace with:
      #   - The container's filesystem as root
      #   - GPU devices (/dev/nvidia*, /dev/dri/*) passed through
      #   - /proc, /sys, /dev mounted appropriately
      #   - Network access (host network namespace)
      #
      gpu-run = pkgs.writeShellScriptBin "gpu-run" ''
        set -euo pipefail

        usage() {
          echo "Usage: gpu-run <command> [args...] <image-ref>"
          echo ""
          echo "Run a command inside an NGC container with GPU passthrough."
          echo ""
          echo "Examples:"
          echo "  gpu-run /bin/bash nvcr.io/nvidia/tritonserver:25.11-py3"
          echo "  gpu-run python -c 'import torch; print(torch.cuda.is_available())' nvcr.io/nvidia/pytorch:25.04-py3"
          echo "  gpu-run nvidia-smi nvcr.io/nvidia/cuda:12.4.0-base-ubuntu22.04"
          echo ""
          echo "Environment variables:"
          echo "  GPU_RUN_KEEP_ROOTFS=1  Keep extracted rootfs after exit"
          echo "  GPU_RUN_ROOTFS=<path>  Use existing rootfs instead of extracting"
          exit 1
        }

        if [ $# -lt 2 ]; then
          usage
        fi

        # Parse arguments: everything except the last arg is the command
        args=("$@")
        image_ref="''${args[-1]}"
        unset 'args[-1]'
        cmd=("''${args[@]}")

        # Validate image ref looks like a container reference
        if [[ ! "$image_ref" =~ ^[a-zA-Z0-9._-]+(\.[a-zA-Z0-9._-]+)*(:[0-9]+)?/[a-zA-Z0-9._/-]+(:[a-zA-Z0-9._-]+)?$ ]]; then
          echo "ERROR: Last argument must be a container image reference"
          echo "       Got: $image_ref"
          echo ""
          usage
        fi

        echo "════════════════════════════════════════════════════════════════"
        echo "  gpu-run — NGC Container with GPU Passthrough"
        echo "════════════════════════════════════════════════════════════════"
        echo ""
        echo "  Image:   $image_ref"
        echo "  Command: ''${cmd[*]}"
        echo ""

        # Check for NVIDIA devices
        if [ ! -e /dev/nvidiactl ]; then
          echo "WARNING: /dev/nvidiactl not found — GPU may not be available"
        fi

        # Setup rootfs
        if [ -n "''${GPU_RUN_ROOTFS:-}" ]; then
          rootfs="$GPU_RUN_ROOTFS"
          echo "Using existing rootfs: $rootfs"
          cleanup_rootfs=false
        else
          rootfs=$(mktemp -d -t gpu-run-rootfs.XXXXXX)
          cleanup_rootfs=true
          
          echo "Extracting container to $rootfs..."
          ${pkgs.crane}/bin/crane export "$image_ref" - | ${pkgs.gnutar}/bin/tar -xf - -C "$rootfs"
          echo "Extraction complete."
        fi
        echo ""

        # Cleanup function
        cleanup() {
          if [ "$cleanup_rootfs" = true ] && [ -z "''${GPU_RUN_KEEP_ROOTFS:-}" ]; then
            echo ""
            echo "Cleaning up rootfs..."
            rm -rf "$rootfs"
          elif [ "$cleanup_rootfs" = true ]; then
            echo ""
            echo "Keeping rootfs at: $rootfs"
            echo "  To reuse: GPU_RUN_ROOTFS=$rootfs gpu-run ..."
          fi
        }
        trap cleanup EXIT

        # Build bwrap arguments
        bwrap_args=(
          # Filesystem: container rootfs as /
          --bind "$rootfs" /
          
          # Essential mounts
          --dev /dev
          --proc /proc
          --tmpfs /tmp
          --tmpfs /run
          
          # Sys filesystem (needed for GPU detection)
          --ro-bind /sys /sys
          
          # DNS resolution
          --ro-bind /etc/resolv.conf /etc/resolv.conf
          
          # NVIDIA devices (if they exist)
        )

        # Add NVIDIA device nodes
        for dev in /dev/nvidia* /dev/nvidiactl /dev/nvidia-uvm /dev/nvidia-uvm-tools; do
          if [ -e "$dev" ]; then
            bwrap_args+=(--dev-bind "$dev" "$dev")
          fi
        done

        # Add DRI devices (for OpenGL/Vulkan)
        if [ -d /dev/dri ]; then
          for dev in /dev/dri/*; do
            if [ -e "$dev" ]; then
              bwrap_args+=(--dev-bind "$dev" "$dev")
            fi
          done
        fi

        # NVIDIA driver libraries from host (if container doesn't have them)
        # This handles the case where the container expects host-mounted drivers
        for lib_path in /usr/lib/x86_64-linux-gnu /usr/lib64; do
          if [ -d "$lib_path" ]; then
            for lib in "$lib_path"/libnvidia*.so* "$lib_path"/libcuda*.so* "$lib_path"/libnvcuvid*.so* "$lib_path"/libnvoptix*.so*; do
              if [ -f "$lib" ]; then
                # Only bind if container doesn't already have this lib
                container_lib="$rootfs$lib"
                if [ ! -f "$container_lib" ]; then
                  bwrap_args+=(--ro-bind "$lib" "$lib")
                fi
              fi
            done
          fi
        done

        # Network: use host network namespace
        bwrap_args+=(--share-net)

        # Environment
        bwrap_args+=(
          --setenv PATH "/usr/local/nvidia/bin:/usr/local/cuda/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
          --setenv LD_LIBRARY_PATH "/usr/local/nvidia/lib64:/usr/local/cuda/lib64:/usr/lib/x86_64-linux-gnu"
          --setenv NVIDIA_VISIBLE_DEVICES "all"
          --setenv NVIDIA_DRIVER_CAPABILITIES "compute,utility"
        )

        # Working directory
        bwrap_args+=(--chdir /root)

        # Unshare namespaces for isolation (but keep network)
        bwrap_args+=(
          --unshare-user
          --unshare-pid
          --unshare-uts
          --unshare-ipc
          --unshare-cgroup
        )

        # Die with parent
        bwrap_args+=(--die-with-parent)

        echo "Entering container..."
        echo ""

        exec ${pkgs.bubblewrap}/bin/bwrap "''${bwrap_args[@]}" -- "''${cmd[@]}"
      '';

      # ════════════════════════════════════════════════════════════════════════
      # 8. vfio-status: Show GPU and IOMMU status
      # ════════════════════════════════════════════════════════════════════════
      vfio-status = pkgs.writeShellScriptBin "vfio-status" ''
        echo "════════════════════════════════════════════════════════════════"
        echo "  VFIO / IOMMU Status"
        echo "════════════════════════════════════════════════════════════════"
        echo ""

        echo "NVIDIA GPUs:"
        ${pkgs.pciutils}/bin/lspci -nn | grep -i nvidia || echo "  (none found)"
        echo ""

        echo "VFIO-bound devices:"
        for dev in /sys/bus/pci/drivers/vfio-pci/*/; do
          [ -d "$dev" ] || continue
          pci=$(basename "$dev")
          [[ "$pci" == "module" || "$pci" == "bind" || "$pci" == "unbind" ]] && continue
          desc=$(${pkgs.pciutils}/bin/lspci -s "$pci" 2>/dev/null || echo "unknown")
          echo "  $desc"
        done
        [ -z "$(ls /sys/bus/pci/drivers/vfio-pci/*/uevent 2>/dev/null)" ] && echo "  (none)"
        echo ""

        echo "IOMMU groups with NVIDIA devices:"
        for grp in /sys/kernel/iommu_groups/*/devices/*; do
          [ -d "$grp" ] || continue
          pci=$(basename "$grp")
          if ${pkgs.pciutils}/bin/lspci -s "$pci" 2>/dev/null | grep -qi nvidia; then
            grp_num=$(echo "$grp" | grep -oP 'iommu_groups/\K[0-9]+')
            echo "  Group $grp_num: $(${pkgs.pciutils}/bin/lspci -s $pci)"
          fi
        done
        echo ""
      '';

    in
    {
      # ════════════════════════════════════════════════════════════════════════
      # Apps (nix run .#<name>)
      # ════════════════════════════════════════════════════════════════════════
      apps = {
        # Primary demo
        demo-broker = {
          type = "app";
          program = "${demo-broker}/bin/demo-broker";
        };

        # Individual components
        gpu-vm = {
          type = "app";
          program = "${gpu-vm}/bin/gpu-vm";
        };
        vsock-bridge = {
          type = "app";
          program = "${vsock-bridge}/bin/vsock-bridge";
        };
        worker-vm = {
          type = "app";
          program = "${worker-vm}/bin/worker-vm";
        };

        # Utilities
        kill-vms = {
          type = "app";
          program = "${kill-vms}/bin/kill-vms";
        };
        broker-test = {
          type = "app";
          program = "${broker-test}/bin/broker-test";
        };
        vfio-status = {
          type = "app";
          program = "${vfio-status}/bin/vfio-status";
        };

        # Container runner with GPU passthrough
        gpu-run = {
          type = "app";
          program = "${gpu-run}/bin/gpu-run";
        };
      };

      # ════════════════════════════════════════════════════════════════════════
      # Packages (for scripting)
      # ════════════════════════════════════════════════════════════════════════
      packages = {
        inherit
          demo-broker
          gpu-vm
          vsock-bridge
          worker-vm
          kill-vms
          broker-test
          vfio-status
          gpu-run
          ;
      };
    };
}
