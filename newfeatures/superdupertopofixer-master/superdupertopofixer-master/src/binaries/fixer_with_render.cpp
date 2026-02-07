#include <sys/stat.h>

#include <chrono>

#include "rendering/OpenGLRenderer.h"
#include "schemes/SDTopoFixer.h"
#include "schemes/TopoFixerSettingsParser.h"

// added for linux
#include <sys/stat.h>
#include <sys/types.h>

//------------------------------------------------------------
// main function
//------------------------------------------------------------

int main(int argc, char** argv) {
	// copy command line arguments into a vector
	std::vector<std::string> args;
	std::copy(argv + 1, argv + argc, std::back_inserter(args));

	// default command line parameter values
	std::string input_params_file = "";
	bool visualization_enabled = true;

	// check for command line parameters
	for (size_t i = 0; i < args.size(); i++) {
		if (args[i].rfind("-input_params=", 0) == 0) {
			input_params_file = args[i].substr(14, 14 + args[i].length());
		} else if (args[i].rfind("-no_visual") == 0) {
			visualization_enabled = false;
		}
	}

	// if there is no input mesh file, and no input parameters file, quit
	struct stat statbuf;
	if (stat(input_params_file.c_str(), &statbuf) == -1) {
		input_params_file = "";
	}
	if (argc == 1 || input_params_file == "") {
		std::cout
		    << "====================================================================================="
		    << std::endl;
		std::cout
		    << "-command line usage: [executable] -input_params=[input parameters file] [-no_visual] "
		    << std::endl;
		std::cout << "-for example: SDTopoFixer/SDTopoFixer -input_params=doublebubble_par.txt ";
		std::cout << "-no input parameters file found, quitting" << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
		exit(1);
	}

	std::cout
	    << "====================================================================================="
	    << std::endl;
	std::cout << "-parsing command line arguments" << std::endl;
	if (input_params_file == "") {
		std::cout << "-input parameters file not loaded" << std::endl;
	} else {
		std::cout << "-using input parameters file: " << input_params_file << std::endl;
	}
	if (visualization_enabled) {
		std::cout << "-visualization: on" << std::endl;
	} else {
		std::cout << "-visualization: off" << std::endl;
	}
	std::cout
	    << "====================================================================================="
	    << std::endl;

	auto parser = TopoFixerSettingsParser::fromFile(input_params_file);
	parser->parse();
	const auto& settings = parser->settings();

	// Check that parameters are correctly specified before doing any work.
	if (settings.should_output_frames) {
		auto output_type = settings.output_type;
		if (settings.output_path.empty()) {
			std::cout << "Cannot write to an empty path, please specify output_path." << std::endl;
			exit(1);
		}
	}

	auto run_mode = settings.run_mode;
	if (run_mode == TopoFixerSettings::RunMode::Render && settings.render_output_path.empty()) {
		std::cout << "Cannot render to an empty path, please specify render_output_path." << std::endl;
		exit(1);
	}

	SDTopoFixer topofixer = SDTopoFixer(settings);
	auto time_step_begin = std::chrono::high_resolution_clock::now();
	if (topofixer.init() != 0) {
		std::cout << "Error encountered when initializing algorithm, quitting\n";
		exit(1);
	}
	auto time_step_init = std::chrono::high_resolution_clock::now();

	if (run_mode == TopoFixerSettings::RunMode::Fixer) {
		topofixer.runFixer(settings.should_perturb_grid);
	} else if (run_mode == TopoFixerSettings::RunMode::Scene) {
		topofixer.runScene();
	} else if (run_mode == TopoFixerSettings::RunMode::Render) {
		OpenGLRenderer::init(&topofixer, 0, 3, true, settings.render_output_path);
		glutMainLoop();
	}

	auto time_step_end = std::chrono::high_resolution_clock::now();
	long long init_time =
	    std::chrono::duration_cast<std::chrono::microseconds>(time_step_init - time_step_begin)
	        .count();
	long long total_sim_time =
	    std::chrono::duration_cast<std::chrono::microseconds>(time_step_end - time_step_init).count();
	std::cout << "-init time: " << init_time / 1000 << "ms" << std::endl;
	std::cout << "-processing time: " << total_sim_time / 1000 << "ms" << std::endl;

	if (settings.should_output_frames) {
		auto output_type = settings.output_type;
		if (output_type == TopoFixerSettings::OutputType::Obj) {
			topofixer.getMesh3DInterface()->writeInObj(settings.output_path);
		} else if (output_type == TopoFixerSettings::OutputType::Bin) {
			topofixer.getMesh3DInterface()->writeInBin(settings.output_path);
		}
	}

	if (visualization_enabled) {
		OpenGLRenderer::init(&topofixer);
		glutMainLoop();
	} else {
		std::cout << "-run ended successfully" << std::endl;
	}

	std::cout
	    << "====================================================================================="
	    << std::endl;
}
