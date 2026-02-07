import numpy as np
import sys

def eatExperiment(file):
    while True:
        line = file.readline().strip()
        if not line:
            break
        elif line.startswith("Experiment finished"):
            break
    return file

def readPress(file):
    stress_file = []
    scale_file = []
    # shear_file = []
    while True:
        line = file.readline().strip();
        if not line:
            break
        elif line.startswith("Scale"):
            scale_file.append([np.float64(i) for i in line.split()[1:]])
        # elif line.startswith("Shear"):
        #     shear_file.append([np.float64(i) for i in line.split()[1:]])
        elif line.startswith("Homogenized stress:"):
            stress_file.append([
                [np.float64(i) for i in file.readline().strip().split()]
                    for j in range(3)
            ])
        elif line.startswith("Experiment finished"):
            break
    stress_file = np.array(stress_file).reshape((-1, 3, 3))
    scale_file = np.array(scale_file).reshape((-1, 3))
    startPress = 0
    for i in range(stress_file.shape[0] - 1):
        if np.linalg.norm(stress_file[i, :, :]) < 1 and\
            np.linalg.norm(stress_file[i+1, :, :]) >= 1 :
            startPress = i
            break
    stress_file = stress_file[startPress:, :, :]
    scale_file = scale_file[startPress:,]
    # experiment = {
    #     "name": "pressTest",
    #     "stress": np.flip(stress_file.reshape((-1, 3, 3)), axis=0),
    #     "scale": np.flip(scale_file.reshape((-1, 3)), axis=0)
    # }
    experiment = {
        "name": "pressTest",
        "stress": stress_file.reshape((-1, 3, 3)),
        "scale": scale_file.reshape((-1, 3))
    }
    # experiment["scale"] /= experiment["scale"][0,:]
    return experiment, file

def readPressShear(file, norm_clamp = 10):
    stress_file = []
    scale_file = []
    # shear_file = []
    while True:
        line = file.readline().strip();
        if not line:
            break
        elif line.startswith("Scale"):
            scale_file.append([np.float64(i) for i in line.split()[1:]])
        # elif line.startswith("Shear"):
        #     shear_file.append([np.float64(i) for i in line.split()[1:]])
        elif line.startswith("Homogenized stress:"):
            stress = np.array([
                [np.float64(i) for i in file.readline().strip().split()]
                    for j in range(3)
            ])
            if np.linalg.norm(stress) < norm_clamp:
                stress = np.zeros_like(stress)
            stress_file.append(stress)
            # stress_file.append([
            #     [np.float64(i) for i in file.readline().strip().split()]
            #         for j in range(3)
            # ])
        elif line.startswith("Experiment finished"):
            break
    stress_file = np.array(stress_file)
    scale_file = np.array(scale_file)
    shearIdx = 0
    for i in range(scale_file.shape[0]):
        if scale_file[i,0] > scale_file[i+1,0]:
            shearIdx = i+1
            break
    experiment = {
        "name": "pressShear",
        "stress": np.flip(stress_file.reshape((-1, shearIdx, 3, 3)), axis=0),
        "scale": np.flip(scale_file.reshape((-1, shearIdx, 3)), axis=0)
    }
    print("Shear", experiment["stress"].shape)
    # experiment["scale"] /= experiment["scale"][0,0,:]
    return experiment, file

ExperimentReader = {
    "Static press shear": readPressShear,
    "Static press": readPress
}

def importExperiments(files: list):
    experiment_files = []
    for filename in files:
        fullFileName = filename
        experiment_files.append([])
        with open(fullFileName, "r") as f:
            while True:
                line = f.readline().strip()
                if not line:
                    break
                elif line.startswith("Starting experiment"):
                    experimentName = " ".join(line.split()[2:])
                    if experimentName in ExperimentReader:
                        experiment_files[-1].append({})
                        experiment_files[-1][-1], f = ExperimentReader[experimentName](f)
                    else:
                        f = eatExperiment(f)
    return experiment_files

def averageExperiments(experiments: list):
    for e in experiments:
        assert len(e) == len(experiments[0])
    avg = []
    for i in range(len(experiments[0])):
        col = [experiments[j][i] for j in range(len(experiments))]
        avgExpt = {
            "name": col[0]["name"]
        }
        stepCount = min(map(lambda a: a["stress"].shape[0], col))
        stresses = [s["stress"][:stepCount, ...] for s in col]
        scales = [s["scale"][:stepCount, ...] for s in col]
        refScales = [s.reshape((-1, 3))[0, :] for s in scales]
        # print([s / s[tuple(0 for d in range(len(s.shape) - 1)), :] for s in scales])
        volume = np.array([
                np.prod(s, axis=(len(s.shape) - 1)) for s in scales
        ])
        volume_sum = np.sum(volume, axis=0)
        
        def volumeReshape(vol, target):
            return vol.reshape(vol.shape + tuple(
                    1 for d in range(len(target.shape) - len(vol.shape))
                    ))
        weightedStress = np.array([s * volumeReshape(w, s)
                 for s, w in zip(stresses, volume)])
        weightedStress = np.sum(weightedStress, axis=0)
        
        weightedStress /= volumeReshape(volume_sum, weightedStress)
        avgExpt["stress"] = weightedStress
        avgExpt["scale"] = np.mean(
                np.array([s / rs for s, rs in zip(scales, refScales)]), axis=0)

        weightedStd = np.array([
            (s - avgExpt["stress"])**2 * volumeReshape(w, s)
            for s, w in zip(stresses, volume)
        ])
        weightedStd = weightedStd.sum(axis=0)
        weightedStd /= volumeReshape(volume_sum, weightedStd)
        weightedStd *= len(experiments) / max(len(experiments) - 1, 1)
        weightedStd = weightedStd**0.5
        avgExpt["std"] = weightedStd


        # Convert to Kirchhoff stress
        avgExpt["stress"] *= volumeReshape(
                avgExpt["scale"].prod(axis=avgExpt["scale"].ndim - 1),
                avgExpt["stress"])
        avg.append(avgExpt)

    return avg


if __name__ == "__main__":
    files = sys.argv[1:]
    experiments = importExperiments(files)
    avg = averageExperiments(experiments)
    # print(experiments[0])

