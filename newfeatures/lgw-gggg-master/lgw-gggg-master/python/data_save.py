def saveObj(filename, hexagons, triangles):
    with open(filename, "w") as f:
        for p in hexagons:
            f.write("v {0} {1} {2}\n".format(p[0]/1e4, p[1]/1e4, p[2]/1e4))
        for t in triangles:
            f.write("f {0}//{0} {1}//{1} {2}//{2}\n".format(t[0]+1, t[1]+1, t[2]+1))

def saveYield(filename, x, y, cubics):
    trunc = x.shape[0] // 10;
    x, y, cubics = x[trunc:], y[trunc:], cubics[trunc:, :]
    with open(filename, "w") as f:
        f.write("{} {} {}\n".format(x[0], x[-1], x.shape[0] - 1))
        for i in range(x.shape[0]):
            f.write("{} {} {} {}\n".format(y[i], cubics[i, 0], cubics[i, 1],
                                           cubics[i, 2]))
    print("Successfully written to file: {}".format(filename))

def saveElasticity(filename, xM, mMod, mCubics, xB, bMod, bCubics):
    with open(filename, "w") as f:
        f.write("{} {} {}\n".format(xM[0], xM[-1], xM.shape[0] - 1))
        for i in range(xM.shape[0]):
            f.write("{} {} {} {}\n".format(mMod[i], mCubics[i, 0], mCubics[i, 1],
                                           mCubics[i, 2]))
        f.write("{} {} {}\n".format(xB[0], xB[-1], xB.shape[0] - 1))
        for i in range(xB.shape[0]):
            f.write("{} {} {} {}\n".format(bMod[i], bCubics[i, 0], bCubics[i, 1],
                                           bCubics[i, 2]))
    print("Successfully written to file: {}".format(filename))
