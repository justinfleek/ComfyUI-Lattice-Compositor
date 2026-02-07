#include <filesystem>
#include <iostream>
#include "TopoViewer.h"
#include "logic/topo_fixer_calls.h"

namespace fs = std::filesystem;
using namespace sdtf::viewer;

int main(int argc, char** argv) {

        // Parse command line arguments for a config file
        // copy command line arguments into a vector
	std::vector<std::string> args;
	std::copy(argv + 1, argv + argc, std::back_inserter(args));

	// default command line parameter values
        const std::string default_input_params_file = "configs/three_balls.cfg";
	std::string input_params_file = "";
        
	// check for command line parameters
	for (size_t i = 0; i < args.size(); i++) {
		if (args[i].rfind("-input_params=", 0) == 0) {
			input_params_file = args[i].substr(14, 14 + args[i].length());
		}
	}

        // Set input file
        if (input_params_file.empty()) {
            std::cout << "-No -input_params file. Loading default scene" << std::endl;
            input_params_file = default_input_params_file;
        }
        if (!fs::exists(input_params_file)) {
            std::cerr << "-Could not find file: " << input_params_file << std::endl;
            std::cerr << "-Exit" << std::endl;
            return 1;
        }
        
        // Start viewer
	TopoViewer viewer(1280, 720, 4);
	auto topo_fixer = logic::loadFromFile(input_params_file);
	if (topo_fixer) {
		viewer.setTopoFixer(std::move(topo_fixer));
	}
	viewer.run();

        return 0;
}
