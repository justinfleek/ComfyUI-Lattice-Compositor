import multiprocessing
import os
import re
import sys

import numpy as np
import plyfile
import scipy
from scipy.spatial.transform import Rotation

dirname = sys.argv[1]
framerate = 24

files = [f for f in os.listdir(dirname) if f.endswith(".npy")]
files.sort(key=lambda f: float(re.search(r"\d+\.?\d+", f).group(0)))
files_rigid = [f for f in files if "rigid" in f]
files = [f for f in files if not "rigid" in f]
print(files_rigid)


def FToRot(k):
    u, _, vh = np.linalg.svd(k[3:].reshape((3, 3)))
    return (u @ vh).flatten()


def writeToPlyFrame(frame, f, fOld):
    a = np.load(os.path.join(dirname, f))
    aOld = np.load(os.path.join(dirname, fOld))
    outputFileName = os.path.join(dirname, "output_%d.ply" % frame)
    if os.path.isfile(outputFileName):
        return

    rot = np.apply_along_axis(FToRot, 1, a)
    q = np.apply_along_axis(
        lambda k: Rotation.from_matrix(k.reshape((3, 3))).as_quat(), 1, rot
    )
    v = (a[:, :3] - aOld[:, :3]) / 0.01
    vertex = np.array(
        [
            (
                a[i, 0],
                a[i, 1],
                a[i, 2],
                q[i, 0],
                q[i, 1],
                q[i, 2],
                q[i, 3],
                v[i, 0],
                v[i, 1],
                v[i, 2],
            )
            for i in range(a.shape[0])
        ],
        dtype=[
            ("x", "f4"),
            ("y", "f4"),
            ("z", "f4"),
            ("q1", "f4"),
            ("q2", "f4"),
            ("q3", "f4"),
            ("q4", "f4"),
            ("v1", "f4"),
            ("v2", "f4"),
            ("v3", "f4"),
        ],
    )
    el = plyfile.PlyElement.describe(vertex, "vertex")
    plyfile.PlyData([el]).write(os.path.join(dirname, "output_%d.ply" % frame))

    vertex = np.array([])


def writeToPlyRigid(frame, f, fOld):
    a = np.load(os.path.join(dirname, f))
    aOld = np.load(os.path.join(dirname, fOld))
    outputFileName = os.path.join(dirname, "output_rigid_%d.ply" % frame)
    if os.path.isfile(outputFileName):
        return

    vertex = np.array(
        [
            (a[i, 0], a[i, 1], a[i, 2], a[i, 3], a[i, 4], a[i, 5], a[i, 6])
            for i in range(a.shape[0])
        ],
        dtype=[
            ("x", "f4"),
            ("y", "f4"),
            ("z", "f4"),
            ("q1", "f4"),
            ("q2", "f4"),
            ("q3", "f4"),
            ("q4", "f4"),
        ],
    )
    el = plyfile.PlyElement.describe(vertex, "vertex")
    plyfile.PlyData([el]).write(outputFileName)

    vertex = np.array([])


n_threads = multiprocessing.cpu_count()
for startFrame in range(0, len(files), n_threads):
    processes = []
    print(startFrame)
    for frame in range(startFrame, min(startFrame + n_threads, len(files))):
        processes.append(
            multiprocessing.Process(
                target=writeToPlyFrame, args=(frame, files[frame], files[frame - 1])
            )
        )
        processes[-1].start()
    for p in processes:
        p.join()
for startFrame in range(0, len(files_rigid), n_threads):
    processes = []
    print(startFrame)
    for frame in range(startFrame, min(startFrame + n_threads, len(files_rigid))):
        processes.append(
            multiprocessing.Process(
                target=writeToPlyRigid,
                args=(frame, files_rigid[frame], files_rigid[frame - 1]),
            )
        )
        processes[-1].start()
    for p in processes:
        p.join()
