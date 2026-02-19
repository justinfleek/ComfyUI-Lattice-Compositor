// s4-runtime // bindings/python/module.cpp
// Main pybind11 module definition.
#include <pybind11/pybind11.h>

namespace py = pybind11;

// Forward declarations for submodule initializers.
void init_dtypes(py::module_& m);
void init_containers(py::module_& m);
void init_core(py::module_& m);

PYBIND11_MODULE(_s4_runtime, m) {
    m.doc() = R"pbdoc(
        s4-runtime: GPU inference runtime library
        -----------------------------------------
        
        Core components:
        - dtypes: Data type vocabulary for GPU inference
        - containers: Specialized containers (unique_vector, disjoint_sets)
        - core: Workspace allocation, serialization, exceptions
    )pbdoc";
    
    m.attr("__version__") = "0.1.0";
    
    // Initialize submodules
    auto dtypes = m.def_submodule("dtypes", "Data type vocabulary");
    init_dtypes(dtypes);
    
    auto containers = m.def_submodule("containers", "Specialized containers");
    init_containers(containers);
    
    auto core = m.def_submodule("core", "Core utilities");
    init_core(core);
}
