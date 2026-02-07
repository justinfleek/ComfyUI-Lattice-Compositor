from numpy.core.getlimits import inf
import data_fitting
import numpy as np
import matplotlib.pyplot as plt

def supersampleCubics(x, y, cubics, n_points=500):
    xPlot = np.linspace(x[0], x[-1], n_points, endpoint=True)
    return xPlot, sampleCubics(xPlot, x, y, cubics)

def sampleCubics(xNew, x, y, cubics):
    yPlot = np.zeros_like(xNew)
    dx = (x[-1] - x[0]) / (x.shape[0] - 1)
    for i, xp in enumerate(xNew):
        if xp < x[0]:
            d = (xp - x[0]) * cubics[-1, 0]
            yPlot[i] = y[0] + d * cubics[0, 2] / cubics[-1, 1]
        elif xp >= x[-1]:
            d = (xp - x[-1]) * cubics[-1, 0]
            yPlot[i] = y[-1] + d * cubics[-2, 2] / cubics[-1, 1]
        else:
            idx = int((xp - x[0]) // dx)
            d = (xp - x[idx]) * cubics[-1, 0]
            yPlot[i] = y[idx] + cubics[idx, :].dot([d**3, d**2, d]) / cubics[-1, 1]
    return yPlot

def sampleCubicsDeriv(_xNew, _x, y, cubics):
    yPlot = np.zeros_like(_xNew)
    xNew = _xNew * cubics[-1, 0]
    x = _x * cubics[-1, 0]
    dx = (x[-1] - x[0]) / (x.shape[0] - 1)
    for i, xp in enumerate(xNew):
        if xp < x[0]:
            d = xp - x[0]
            yPlot[i] = cubics[0, 2]
        elif xp >= x[-1]:
            d = xp - x[-1]
            yPlot[i] = cubics[-2, 2]
        else:
            idx = int((xp - x[0]) // dx)
            d = (xp - x[idx])
            yPlot[i] = cubics[idx, :].dot([3 * d * d, 2 * d, 1])
        yPlot[i] *= cubics[-1, 0] / cubics[-1, 1]
    return yPlot

def plotMohr(positions, radii, extX, extY, cubics):
    plt.figure()
    extents = [positions.min(), radii.max()]
    plt.axis([extents[0] - extents[1], 0, -extents[1], extents[1]])

    plt.axis("equal")
    plt.scatter(positions, radii, s=1)
    plt.plot([0, 1.1 * positions.min()], [0, -1.1 * positions.min()], color="gray", label="Here there be adhesion")

    xPlot, yPlot = supersampleCubics(extX, extY, cubics)

    plt.plot(xPlot, yPlot, color="red", linewidth=4, label="Interpolated")
    plt.plot(extX, extY, color="orange", linewidth=2, linestyle="--", marker=".", ms=10, label="Exterior points")

    r_coeff = extY.dot(extX) / extX.dot(extX)
    f_coeff = -r_coeff / ((1 - r_coeff * r_coeff)**0.5)
    print(r_coeff, f_coeff)
    plt.plot([0, positions.min()], [0, r_coeff * positions.min()], linestyle="--", color="brown", label="mu="+str(f_coeff))

    initSlope = cubics[-2, 2]
    f_coeff = -initSlope / ((1 - initSlope * initSlope)**0.5)
    plt.plot([0, positions.min()], [0, initSlope * positions.min()], linestyle="--", label="mu="+str(f_coeff))
    plt.legend()

def plotElastic(stresses, deform, stdDer):
    dCrop = np.flip(deform, axis=0)
    sCrop = np.flip(stresses, axis=0)
    sCrop[-1,:] = 0
    
    volDev, mMod, mCubic, logVol, bMod, bCubic = data_fitting.fitExtendedHenckyElasticity(dCrop, sCrop)
    print(volDev)

    plt.figure()
    devFromVol = 2. / 3. * logVol * logVol
    # plt.plot(-(1.5 * volDev) ** 0.5, mMod, label="mu")
    plt.plot(logVol, sampleCubics(devFromVol, volDev, mMod, mCubic), label="mu")
    plt.plot(volDev, sampleCubics(volDev, volDev, mMod, mCubic), label="mu")
    plt.plot(logVol, bMod, label="B")
    plt.xlabel("log(VOLUME)")
    plt.ylabel("moduli")
    plt.legend()

    hencky = np.log(dCrop)
    henckyDev = hencky - logVol.reshape((-1, 1)) / 3
    devNorm = (henckyDev * henckyDev).sum(axis=1)

    mModNew = sampleCubics(devNorm, volDev, mMod, mCubic)
    mDeriv = sampleCubicsDeriv(devNorm, volDev, mMod, mCubic)

    bDeriv = bCubic[:-1,-1] * bCubic[-1, 0] / bCubic[-1, 1]

    stressNew = 2 * (mDeriv * devNorm + mModNew).reshape((-1, 1)) * henckyDev
    stressNew += ((bDeriv * logVol + 2 * bMod) * logVol).reshape((-1, 1))

    plt.figure()
    plt.plot(dCrop[:,1], stressNew[:,0], label="sigma_{11} (Reconstructed)")
    plt.plot(dCrop[:,1], stressNew[:,1], label="sigma_{22} (Reconstructed)")
    plt.scatter(dCrop[:,1], sCrop[:, 0,0], label="sigma_{11} (Measured)")
    plt.scatter(dCrop[:,1], sCrop[:, 1,1], label="sigma_{22} (Measured)")
    plt.scatter(dCrop[:,1], sCrop[:, 2,2], label="sigma_{33} (Measured)")
    plt.xlabel("Strain")
    plt.ylabel("Stress")

    plt.legend()

def yieldSurfaceMesh(x, y, cubics, samples=500):
    extX, extY = supersampleCubics(x, y, cubics, samples)
    points = np.array([
        ([k + r, k + r, k - r],
        [k + r, k - r, k - r],
        [k + r, k - r, k + r],
        [k - r, k - r, k + r],
        [k - r, k + r, k + r],
        [k - r, k + r, k - r]) for (k, r) in zip(extX, extY)
    ]).reshape((-1,3))
    triangles = np.array(
            list(map(lambda i: [[i, i+1, i+7], [i, i+7, i+6]] if i%6 != 5 else
                [[i, i-5, i+1], [i, i+1, i+6]], range(points.shape[0]-6)))
    ).reshape((-1, 3))
    return points, triangles

def plotPrincipleSpace(_stresses):
    stresses = _stresses.reshape((-1, 3, 3))
    sevals = np.array([np.sort(np.linalg.eig(s)[0]) for s in stresses])

    fig = plt.figure()
    ax = fig.add_subplot(projection='3d')
    
    ax.scatter(sevals[:,0], sevals[:,1], sevals[:,2], s=30)
    ax.scatter(sevals[:,0], sevals[:,2], sevals[:,1], s=30)
    ax.scatter(sevals[:,1], sevals[:,0], sevals[:,2], s=30)
    ax.scatter(sevals[:,1], sevals[:,2], sevals[:,0], s=30)
    ax.scatter(sevals[:,2], sevals[:,0], sevals[:,1], s=30)
    ax.scatter(sevals[:,2], sevals[:,1], sevals[:,0], s=30)
    
def plotYieldSurface(p, r, cubics, search_factor=50):
    hexagons, triangles = yieldSurfaceMesh(p, r, cubics)
    fig = plt.figure()
    ax = fig.add_subplot(projection='3d')
    ax.plot_trisurf(hexagons[:,0], hexagons[:,1], hexagons[:,2], triangles=triangles, linewidth=0)

