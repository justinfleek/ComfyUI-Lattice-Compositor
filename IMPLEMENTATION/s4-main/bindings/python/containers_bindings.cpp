// s4-runtime // bindings/python/containers_bindings.cpp
// Python bindings for container types.
#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/operators.h>

#include <s4/containers/unique_vector.h>
#include <s4/containers/disjoint_sets.h>

#include <unordered_map>

namespace py = pybind11;
using namespace s4::containers;

void init_containers(py::module_& m) {
    // unique_vector<int>
    py::class_<unique_vector<int>>(m, "UniqueVectorInt",
            R"pbdoc(
            Vector that maintains uniqueness via backing set.
            Provides O(1) lookup with deterministic iteration order.
            
            Invariants:
            - No duplicate entries
            - Size equals number of unique elements inserted
            - Iteration order matches insertion order (for first occurrence)
            )pbdoc")
        .def(py::init<>())
        .def(py::init<std::initializer_list<int>>())
        .def(py::init([](const std::vector<int>& v) {
            return unique_vector<int>(v.begin(), v.end());
        }), py::arg("values"))
        .def("push_back", py::overload_cast<const int&>(&unique_vector<int>::push_back),
             py::arg("entry"), "Insert element, returns True if inserted")
        .def("contains", &unique_vector<int>::contains, py::arg("entry"),
             "Check if element exists")
        .def("has", &unique_vector<int>::has, py::arg("entry"),
             "Alias for contains()")
        .def("intersect", &unique_vector<int>::intersect, py::arg("other"),
             "Compute intersection preserving this container's order")
        .def("has_intersection", &unique_vector<int>::has_intersection, py::arg("other"),
             "Check if any element exists in both containers")
        .def("subtract", &unique_vector<int>::subtract, py::arg("other"),
             "Compute set difference (elements in this but not in other)")
        .def("unite", &unique_vector<int>::unite, py::arg("other"),
             "Compute union of both containers")
        .def("erase", &unique_vector<int>::erase, py::arg("entry"),
             "Remove element, returns count of removed elements")
        .def("clear", &unique_vector<int>::clear, "Clear all elements")
        .def("pop_back", &unique_vector<int>::pop_back, "Remove and return last element")
        .def("front", &unique_vector<int>::front, "Get first element")
        .def("back", &unique_vector<int>::back, "Get last element")
        .def("empty", &unique_vector<int>::empty, "Check if empty")
        .def("__len__", &unique_vector<int>::size)
        .def("__contains__", &unique_vector<int>::contains)
        .def("__iter__", [](const unique_vector<int>& v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const unique_vector<int>& v, std::size_t i) {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        })
        .def("__eq__", &unique_vector<int>::operator==)
        .def("__ne__", &unique_vector<int>::operator!=)
        .def("__repr__", &unique_vector<int>::to_string)
        .def("copy", [](const unique_vector<int>& v) {
            return unique_vector<int>(v);
        }, "Create a deep copy")
        .def("to_list", [](const unique_vector<int>& v) {
            return std::vector<int>(v.begin(), v.end());
        }, "Convert to Python list");
    
    // unique_vector<std::string>
    py::class_<unique_vector<std::string>>(m, "UniqueVectorStr",
            "String variant of unique_vector")
        .def(py::init<>())
        .def(py::init([](const std::vector<std::string>& v) {
            return unique_vector<std::string>(v.begin(), v.end());
        }), py::arg("values"))
        .def("push_back", py::overload_cast<const std::string&>(
             &unique_vector<std::string>::push_back),
             py::arg("entry"), "Insert element, returns True if inserted")
        .def("contains", &unique_vector<std::string>::contains, py::arg("entry"))
        .def("has", &unique_vector<std::string>::has, py::arg("entry"))
        .def("intersect", &unique_vector<std::string>::intersect, py::arg("other"))
        .def("has_intersection", &unique_vector<std::string>::has_intersection, 
             py::arg("other"))
        .def("subtract", &unique_vector<std::string>::subtract, py::arg("other"))
        .def("unite", &unique_vector<std::string>::unite, py::arg("other"))
        .def("erase", &unique_vector<std::string>::erase, py::arg("entry"))
        .def("clear", &unique_vector<std::string>::clear)
        .def("pop_back", &unique_vector<std::string>::pop_back)
        .def("front", &unique_vector<std::string>::front)
        .def("back", &unique_vector<std::string>::back)
        .def("empty", &unique_vector<std::string>::empty)
        .def("__len__", &unique_vector<std::string>::size)
        .def("__contains__", &unique_vector<std::string>::contains)
        .def("__iter__", [](const unique_vector<std::string>& v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const unique_vector<std::string>& v, std::size_t i) {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        })
        .def("__eq__", &unique_vector<std::string>::operator==)
        .def("__ne__", &unique_vector<std::string>::operator!=)
        .def("__repr__", &unique_vector<std::string>::to_string)
        .def("to_list", [](const unique_vector<std::string>& v) {
            return std::vector<std::string>(v.begin(), v.end());
        });
    
    // disjoint_sets<int>
    py::class_<disjoint_sets<int>>(m, "DisjointSetsInt",
            R"pbdoc(
            Union-find data structure for managing equivalence relationships.
            Elements are grouped into disjoint sets; sets can be merged.
            
            Invariants:
            - Each element belongs to exactly one set
            - Sets are non-empty
            - Reflexivity: x ~ x for all mapped x
            - Symmetry: x ~ y implies y ~ x
            - Transitivity: x ~ y and y ~ z implies x ~ z
            )pbdoc")
        .def(py::init<>())
        .def(py::init<const disjoint_sets<int>&>(), py::arg("other"),
             "Deep copy constructor")
        .def("copy", [](const disjoint_sets<int>& ds) {
            return disjoint_sets<int>(ds);
        }, "Create a deep copy")
        .def("make_set", [](disjoint_sets<int>& ds, int entry) {
            auto [it, inserted] = ds.initialize_set(entry);
            return inserted;
        }, py::arg("entry"), "Initialize a singleton set, returns True if new")
        .def("initialize_set", [](disjoint_sets<int>& ds, int entry) {
            auto [it, inserted] = ds.initialize_set(entry);
            return inserted;
        }, py::arg("entry"), "Initialize a singleton set, returns True if new")
        .def("union_sets", &disjoint_sets<int>::map_entries,
             py::arg("entry0"), py::arg("entry1"),
             "Merge the sets containing entry0 and entry1")
        .def("map_entries", &disjoint_sets<int>::map_entries,
             py::arg("entry0"), py::arg("entry1"),
             "Merge the sets containing entry0 and entry1")
        .def("are_equivalent", &disjoint_sets<int>::permissive_are_mapped,
             py::arg("entry0"), py::arg("entry1"),
             "Check if two entries are in the same set (returns False if either missing)")
        .def("strict_are_mapped", &disjoint_sets<int>::strict_are_mapped,
             py::arg("entry0"), py::arg("entry1"),
             "Check if two entries are in the same set (entry0 must exist)")
        .def("permissive_are_mapped", &disjoint_sets<int>::permissive_are_mapped,
             py::arg("entry0"), py::arg("entry1"),
             "Check if two entries are in the same set (returns False if either missing)")
        .def("mapping_exists", &disjoint_sets<int>::mapping_exists, py::arg("entry"),
             "Check if entry exists in any set")
        .def("erase", &disjoint_sets<int>::erase, py::arg("entry"),
             "Remove entry from sets, returns True if found")
        .def("clear", &disjoint_sets<int>::clear, "Clear all sets")
        .def("empty", &disjoint_sets<int>::empty, "Check if empty")
        .def("__len__", &disjoint_sets<int>::size, "Number of disjoint sets")
        .def("__repr__", &disjoint_sets<int>::to_string)
        .def("all_elements", [](const disjoint_sets<int>& ds) {
            auto uv = ds.all_elements();
            return std::vector<int>(uv.begin(), uv.end());
        }, "Get all elements across all sets")
        .def("get_set_of", [](const disjoint_sets<int>& ds, int entry) {
            const auto& uv = ds.get_set_of(entry);
            return std::vector<int>(uv.begin(), uv.end());
        }, py::arg("entry"), "Get the set containing entry")
        .def("get_all_sets", [](const disjoint_sets<int>& ds) {
            std::vector<std::vector<int>> result;
            for (const auto& set : ds.sets()) {
                result.emplace_back(set->begin(), set->end());
            }
            return result;
        }, "Get all sets as list of lists")
        .def("get_mapping", [](const disjoint_sets<int>& ds) {
            // Return a dict mapping each element to its set's first element (representative).
            std::unordered_map<int, int> result;
            for (const auto& [entry, set_ptr] : ds.map()) {
                if (set_ptr && !set_ptr->empty()) {
                    result[entry] = set_ptr->front();
                }
            }
            return result;
        }, "Get mapping from each element to its set representative");
    
    // disjoint_sets<std::string>
    py::class_<disjoint_sets<std::string>>(m, "DisjointSetsStr",
            "String variant of disjoint_sets")
        .def(py::init<>())
        .def(py::init<const disjoint_sets<std::string>&>(), py::arg("other"))
        .def("initialize_set", [](disjoint_sets<std::string>& ds, 
                                  const std::string& entry) {
            auto [it, inserted] = ds.initialize_set(entry);
            return inserted;
        }, py::arg("entry"))
        .def("map_entries", &disjoint_sets<std::string>::map_entries,
             py::arg("entry0"), py::arg("entry1"))
        .def("strict_are_mapped", &disjoint_sets<std::string>::strict_are_mapped,
             py::arg("entry0"), py::arg("entry1"))
        .def("permissive_are_mapped", &disjoint_sets<std::string>::permissive_are_mapped,
             py::arg("entry0"), py::arg("entry1"))
        .def("mapping_exists", &disjoint_sets<std::string>::mapping_exists, 
             py::arg("entry"))
        .def("erase", &disjoint_sets<std::string>::erase, py::arg("entry"))
        .def("clear", &disjoint_sets<std::string>::clear)
        .def("empty", &disjoint_sets<std::string>::empty)
        .def("__len__", &disjoint_sets<std::string>::size)
        .def("__repr__", &disjoint_sets<std::string>::to_string)
        .def("all_elements", [](const disjoint_sets<std::string>& ds) {
            auto uv = ds.all_elements();
            return std::vector<std::string>(uv.begin(), uv.end());
        })
        .def("get_set_of", [](const disjoint_sets<std::string>& ds, 
                              const std::string& entry) {
            const auto& uv = ds.get_set_of(entry);
            return std::vector<std::string>(uv.begin(), uv.end());
        }, py::arg("entry"))
        .def("get_all_sets", [](const disjoint_sets<std::string>& ds) {
            std::vector<std::vector<std::string>> result;
            for (const auto& set : ds.sets()) {
                result.emplace_back(set->begin(), set->end());
            }
            return result;
        });
}
