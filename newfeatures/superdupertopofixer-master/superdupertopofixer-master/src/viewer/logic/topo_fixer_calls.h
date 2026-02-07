#pragma once

#include <memory>

#include "schemes/SDTopoFixer.h"
#include "schemes/TopoFixerSettingsParser.h"

namespace sdtf::viewer::logic {
;

// Reads a TopoFixer parameter file, runs the TopoFixer application, and returns the final TopoFixer
// datastructure. If the parameter file was not found, or contained errors, a null pointer is
// returned.
std::unique_ptr<SDTopoFixer> loadFromFile(std::string input_path);

}  // namespace sdtf::viewer::logic