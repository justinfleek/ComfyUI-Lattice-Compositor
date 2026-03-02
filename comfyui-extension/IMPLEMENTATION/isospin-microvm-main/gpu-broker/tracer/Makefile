# NVIDIA Driver Trace Shim
# Build: make
# Clean: make clean

CC ?= gcc
CFLAGS = -Wall -Wextra -O2 -fPIC -D_GNU_SOURCE
LDFLAGS = -shared -ldl -lpthread

TARGET = libnv_trace.so
SOURCE = nv_trace.c

.PHONY: all clean test

all: $(TARGET)

$(TARGET): $(SOURCE)
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

clean:
	rm -f $(TARGET)

# Test with nvidia-smi
test: $(TARGET)
	@echo "Testing with nvidia-smi..."
	LD_PRELOAD=./$(TARGET) NV_TRACE_FILE=/tmp/test_trace.json NV_TRACE_VERBOSE=1 nvidia-smi -L || true
	@echo ""
	@echo "Trace output:"
	@cat /tmp/test_trace.json | head -50
	@echo "..."

# Test with verbose output
test-verbose: $(TARGET)
	LD_PRELOAD=./$(TARGET) NV_TRACE_FILE=/tmp/test_trace.json NV_TRACE_VERBOSE=1 nvidia-smi

# Test with redzones enabled
test-redzone: $(TARGET)
	LD_PRELOAD=./$(TARGET) NV_TRACE_FILE=/tmp/test_trace.json NV_TRACE_REDZONE=1 NV_TRACE_VERBOSE=1 nvidia-smi -L
