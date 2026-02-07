#include <filesystem>
#include <iostream>

#include "UI/SimulationSceneCLI.h"
#include "IO/FileLoader.h"
#include "IO/FileSaver.h"

int main(int argc, char* argv[]) {
	std::string m_sceneFileName = "";
	// std::string m_outputFileName = "";
	Homogenization::IO::FileLoader m_fileLoader;
	// ContactSimulation::IO::FileSaver m_fileSaver;

	Homogenization::UI::SimulationSceneCLI m_scene3D;

	std::string m_collisionOutput = "";
	bool m_allset = false;
	if (argc >= 2) {
		m_sceneFileName = std::filesystem::path(argv[1]);
		// m_outputFileName = std::filesystem::path(argv[2]);
		m_fileLoader.loadFile(m_scene3D, m_sceneFileName, false);
		m_allset = true;
	}
	if (m_allset == true) {
		m_scene3D.setSimulate(true);
		while (m_scene3D.isSimulating()) {
			m_scene3D.advanceOneFrame();
		}
		std::cout << "Experiments finished. Exiting..." << std::endl;
		// m_fileSaver.saveToFile(m_scene3D.dynamicSystem(), m_outputFileName);
	}

	return 0;
}
