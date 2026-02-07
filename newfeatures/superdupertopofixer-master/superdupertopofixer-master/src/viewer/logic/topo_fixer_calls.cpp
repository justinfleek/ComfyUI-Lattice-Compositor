#include "topo_fixer_calls.h"

namespace sdtf::viewer::logic {
;

std::unique_ptr<SDTopoFixer> loadFromFile(std::string input_path) {
        // Parse config file
	auto parser = TopoFixerSettingsParser::fromFile(input_path);
	if (!parser) {
		return nullptr;
        }
	parser->parse();
	const TopoFixerSettings& settings = parser->settings();
        
	auto topo_fixer = std::make_unique<SDTopoFixer>(settings);
	if (topo_fixer->init() != 0) {
		return nullptr;
	}

	return topo_fixer;
}

}  // namespace sdtf::viewer::logic
