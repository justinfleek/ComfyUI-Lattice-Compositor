import data_input
import data_fitting
import data_vis
import data_save
import sys
import numpy as np
import matplotlib.pyplot as plt

def plotShear(stresses, scale, shear):
    stressesDiff = stresses[:,1:,0,1] - stresses[:,:-1,0,1]
    shearDiff = (shear[:,1:,0] - shear[:,:-1,0])
    fig = plt.figure()
    ax = fig.add_subplot(projection='3d')
    ax.scatter(scale[:,:,1], shear[:,:,0], stresses[:,:,0,1])

    fig = plt.figure()
    ax = fig.add_subplot(projection='3d')
    print(stressesDiff.shape, shearDiff.shape)
    ax.scatter(scale[:,1:,1], shear[:,1:,0], stressesDiff/shearDiff)

    press = (stresses[:,0,0,0] + stresses[:,0,1,1] + stresses[:,0,2,2]) / 3
    bulkMods = (press[:-1] - press[1:]) / (scale[:-1,0,1] - scale[1:,0,1])
    devx = stresses[:,0,0,0] - press
    devy = stresses[:,0,1,1] - press
    devz = stresses[:,0,2,2] - press
    shearModX = -3 * (devx[:-1] - devx[1:]) / (scale[:-1,0,1]-scale[1:,0,1]) / 2
    shearModY = 3 * (devy[:-1] - devy[1:]) / (scale[:-1,0,1]-scale[1:,0,1]) / 4
    shearModZ = -3 * (devz[:-1] - devz[1:]) / (scale[:-1,0,1]-scale[1:,0,1]) / 2
    shearMods = (shearModX + shearModY + shearModZ) / 3
    # shearMods = (devSum[:-1] - devSum[1:]) / ((scale[1:,0,1] - scale[:-1,0,1]) * 4)
    plt.figure()
    plt.plot(scale[:,0,1] - 1, stresses[:,0,0,0])
    plt.plot(scale[:,0,1] - 1, stresses[:,0,1,1])
    plt.plot(scale[:,0,1] - 1, stresses[:,0,2,2])
    plt.plot(scale[:,0,1] - 1, stresses[:,0,0,1])
    plt.plot(scale[:,0,1] - 1, stresses[:,0,0,2])
    plt.plot(scale[:,0,1] - 1, stresses[:,0,1,2])
    # plt.figure()
    # plt.plot(scale[:,0,1] - 1, stresses[:,0,0,0] - press)
    # plt.plot(scale[:,0,1] - 1, stresses[:,0,1,1] - press)
    # plt.plot(scale[:,0,1] - 1, stresses[:,0,2,2] - press)
    plt.figure()
    plt.plot(scale[1:,0,1] - 1, shearMods, label="Shear modulus (press test)")
    plt.plot(scale[:,0,1] - 1, stressesDiff[:,0]/shearDiff[:,0], label="Shear mudulus (shear test)")
    plt.plot(scale[1:,0,1] - 1, bulkMods, label="Bulk modulus")
    plt.xlabel("Strain")
    plt.legend()

    fig = plt.figure()
    ax = fig.add_subplot(projection='3d')
    ax.scatter(scale[:,:,1], shear[:,:,0], np.sqrt(stresses[:,:,1,0]**2 + stresses[:,:,1,2]**2)/stresses[:,:,1,1])


results = data_input.averageExperiments(
        data_input.importExperiments(sys.argv[1:])
        )

stresses = data_fitting.extractPressShearStresses(results)
circles = data_fitting.mohrCircles(stresses)
extX, extY, cubics = data_fitting.exteriorPoints(circles[0], circles[1], search_factor=50)
data_vis.plotMohr(circles[0], circles[1], extX, extY, cubics)
# plt.savefig("savedfig.png")
# data_vis.plotElastic(results[2]["stress"], results[2]["scale"], results[2]["std"])
# plotShear(stresses, scale, shear)

# data_vis.plotPrincipleSpace(stresses[::10, :, :])
# data_vis.plotYieldSurface(extX, extY, cubics)

data_save.saveYield("out.txt", extX, extY, cubics)
plt.show()

