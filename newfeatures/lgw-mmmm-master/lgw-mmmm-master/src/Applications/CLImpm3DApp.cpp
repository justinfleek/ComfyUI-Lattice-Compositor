#include <iomanip>

#include "CLImpm3DApp.hpp"
#include "IO/ParticlePLYExport.hpp"
#include "IO/SimulationGenerator.hpp"

#define USE_TIMER
#include "Common/timer.hpp"

CLIMpm3DApp::CLIMpm3DApp(ConfigFileLoader& config)
    : m_particleSaveFreq(config.output.freq),
      m_outputDirectory(config.output.fsPath) {
    TIMER_MS_START("[Init]", 0);
    SimulationGenerator<false> sim;
    m_mpmSimPtr = sim.initializeSimulation(config);
    TIMER_MS_END;
}

int CLIMpm3DApp::exec() {
    // Update particles and so on here
    // m_simulationPaused = false;
    while (!m_mpmSimPtr->isFinished()) {
        updateSystem();
    }
    return 0;
}

void CLIMpm3DApp::updateSystem() {
    // Compute
    auto saveFile = [&]() {
        std::vector<Type::NumT> data;
        NumT time;

        m_mpmSimPtr->dumpParticleData(data, time, true);
        std::stringstream ss;
        ss << m_outputDirectory.string() << "/out_" << std::setw(4)
           << std::setfill('0') << m_stepCounter << ".ply";
        std::string outputFile = ss.str();

        exportDataToPLY(outputFile, false, true, data);
        std::cout << "Saved result to: " << outputFile << std::endl;

        if (m_mpmSimPtr->getRigidBodyWorld()) {
            data.clear();
            m_mpmSimPtr->dumpRigidData(data, time);
            ss.str("");
            ss << m_outputDirectory.string() << "/out_rigid_" << std::setw(4)
               << std::setfill('0') << m_stepCounter << ".ply";
            outputFile = ss.str();
            exportDataToPLY(outputFile, false, true, data);
            std::cout << "Saved rigid body result to: " << outputFile
                      << std::endl;
        }
    };
    if (!m_mpmSimPtr->isFinished()) {
        if (m_mpmSimPtr->getCurrentSimTime() == 0 && m_particleSaveFreq) {
            saveFile();
        }
        // for (size_t n = 0; n < m_stepsPerFrame; ++n) {
        TIMER_MS_START("[App]", 0);
        m_mpmSimPtr->step();
        TIMER_MS_PRINT_CP("Simulation loop");
        TIMER_MS_END;

        m_stepCounter++;
        if ((m_particleSaveFreq > 0) &&
            (!(m_stepCounter % m_particleSaveFreq))) {
            saveFile();
        }
        // }  // n
    } else {
        m_mpmSimPtr->step();
    }
}

int main(int argc, char** argv) {
    // Look for a config file argument
    std::string confFilename = "";
    for (int i = 0; i < argc; ++i) {
        std::string arg(argv[i]);
        if (arg.ends_with(".json") || arg.ends_with(".jsonc")) {
            confFilename = arg;
            break;
        }
    }  // i
    if (confFilename == "") {
        std::cerr << "No configuration file provided" << std::endl;
        return EXIT_FAILURE;
    }

    // Load config
    ConfigFileLoader config(confFilename, false);

    // Create GUI App
    CLIMpm3DApp app(config);

    return app.run();
}
