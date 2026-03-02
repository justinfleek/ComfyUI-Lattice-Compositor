# SPDX-License-Identifier: MIT
#
# Makefile for nvidia-shim.ko
#
# Usage:
#   make                    - build GUEST mode (shim in VM, broker on host)
#   make NV_SHIM_HOST=1     - build HOST mode (shim on host, GPU VM has broker)
#   make KDIR=/path/to/src  - build against specific kernel
#   make clean              - clean build artifacts
#   make install            - install to /lib/modules/$(uname -r)/extra/
#
# Modes:
#   GUEST mode (default): Run in VM, connect to host broker (CID=2)
#   HOST mode:            Run on host, connect to GPU VM's broker (CID=guest)
#

obj-m := nvidia-shim.o

KDIR ?= /lib/modules/$(shell uname -r)/build
PWD := $(shell pwd)

# Build mode: 0=guest (default), 1=host
NV_SHIM_HOST ?= 0

# Extra compiler flags
ccflags-y := -Wall -Werror -DNV_SHIM_HOST=$(NV_SHIM_HOST)

.PHONY: all clean install

all:
	$(MAKE) -C $(KDIR) M=$(PWD) modules

clean:
	$(MAKE) -C $(KDIR) M=$(PWD) clean

install:
	$(MAKE) -C $(KDIR) M=$(PWD) modules_install
	depmod -a

# For development: load/unload
.PHONY: load unload reload

load:
	insmod nvidia-shim.ko

unload:
	rmmod nvidia-shim

reload: unload load

# Test with vsock parameters
.PHONY: load-test

load-test:
	@echo "nvidia-shim build mode: $(if $(filter 1,$(NV_SHIM_HOST)),HOST,GUEST)"
	@echo ""
	@echo "Parameters:"
	@echo "  broker_cid   - vsock CID to connect to"
	@echo "  broker_port  - vsock port (default: 9999)"
	@echo ""
ifeq ($(NV_SHIM_HOST),1)
	@echo "HOST mode - shim on host, GPU VM has real driver + broker"
	@echo "Example:"
	@echo "  insmod nvidia-shim.ko broker_cid=3 broker_port=9999"
	@echo "  (where CID=3 is your GPU VM's vsock CID)"
else
	@echo "GUEST mode - shim in VM, host has broker"
	@echo "Example:"
	@echo "  insmod nvidia-shim.ko broker_cid=2 broker_port=9999"
	@echo "  (CID=2 is always the host)"
endif

# Quick test - load with defaults
.PHONY: load-default

load-default:
ifeq ($(NV_SHIM_HOST),1)
	@echo "HOST mode: must specify broker_cid=<guest VM CID>"
	@echo "Example: insmod nvidia-shim.ko broker_cid=3 broker_port=9999"
else
	insmod nvidia-shim.ko broker_cid=2 broker_port=9999
endif

# Convenience targets for each mode
.PHONY: guest host

guest:
	$(MAKE) NV_SHIM_HOST=0

host:
	$(MAKE) NV_SHIM_HOST=1
