// s4 // attention/sage_attention_plugin.cu
// Instantiation unit for SageAttention TensorRT plugin.
// The plugin implementation is header-only in sage_attention_plugin.h.

#include <s4/attention/sage_attention_plugin.h>

// Plugin registration happens via REGISTER_TENSORRT_PLUGIN in the header.
// This translation unit exists to ensure the plugin is linked.
