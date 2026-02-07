from matplotlib.cbook import _premultiplied_argb32_to_unmultiplied_rgba8888
import numpy as np
import matplotlib.pyplot as plt
import data_vis

def extractPressShearStresses(experiments: list):
    stresses = np.zeros((0, 3, 3))
    for expt in experiments:
        if expt["name"] == "pressShear":
            stresses = np.concatenate(
                    (stresses, expt["stress"].reshape((-1,3,3))), axis=0)
    return stresses

def extractPressStresses(experiments: list):
    stresses = [expt["stress"] for expt in filter(lambda a: a["name"] == "pressTest", experiments)]
    scale = [expt["scale"] for expt in filter(lambda a: a["name"] == "pressTest", experiments)]
    scale = np.array(scale).reshape((-1, 3))
    stresses = np.array(stresses).reshape((-1, 3, 3))
    return np.flip(scale, axis=0), np.flip(stresses, axis=0)

def mohrCircles(_stresses):
    stresses = _stresses.reshape((-1, 3, 3))
    sevals = np.array([np.sort(np.linalg.eig(s)[0]) if np.isfinite(s).all() else [0, 0, 0] for s in stresses])

    positions, radii = (
            np.reshape((sevals[:,2] + sevals[:,0]) * 0.5, (-1)),
            np.reshape((sevals[:,2] - sevals[:,0]) * 0.5, (-1))
             )
    return positions, radii

def pressureDef(_stresses):
    stresses = _stresses.reshape((-1, 3, 3))
    sevals = np.array([np.sort(np.linalg.eig(s)[0]) if np.isfinite(s).all() else [0, 0, 0] for s in stresses])

    p = sevals.mean(axis=1)
    dev = np.linalg.norm(sevals - p.reshape((-1,1)), axis=1)
    return p, dev

def exteriorPoints(x, y, search_factor=50, max_slope=3):
    # Sort the points
    idx = np.argsort(x);
    x_sorted = x[idx]
    y_sorted = y[idx]
    # x_sorted = x_sorted[x_sorted.shape[0]//10:]
    # y_sorted = y_sorted[y_sorted.shape[0]//10:]

    search_radius = (x_sorted[-1] - x_sorted[0]) / search_factor
    curvePoints = [0]
    id = 0
    search_radius_curr = search_radius
    outliers = np.zeros_like(x_sorted)
    while id < x_sorted.shape[0]:
        # Find maximum range of possible points
        nextExtPoint = id
        currPoint = np.array([x_sorted[id], y_sorted[id]])
        
        nextPointCand = x_sorted.shape[0] - 1;
        for idNext in range(id+2, x_sorted.shape[0]):
            nextPoint = np.array([x_sorted[idNext], y_sorted[idNext]])

            if nextPoint[0] - currPoint[0] > search_radius_curr and outliers[idNext] == False:
                nextPointCand = idNext - 1;
                break;
        
        # If the final point is an outlier (edge case), terminate the algorithm
        if (nextPointCand == x_sorted.shape[0] - 1 and outliers[nextPointCand] == True):
            curvePoints.append(nextPointCand)
            break
        # If no further points can be reached, terminate the algorithm
        if (nextPointCand == id):
            break
        
        # Initialize slope to -inf (expressed as two numbers to prevent NaNs)
        maxSlopeX = 1
        maxSlopeY = -np.inf

        # Find the furthest point in range such that no intersections occur
        # on a straight line. This is equivalent to finding the maximum slope
        # in the range.
        for incNext in range(id + 1, nextPointCand + 1):
            if (outliers[incNext]):
                continue
            nextPoint = np.array([x_sorted[incNext], y_sorted[incNext]])
            slopeX = nextPoint[0] - currPoint[0]
            slopeY = nextPoint[1] - currPoint[1]
            
            # Remove near vertical drops and overlapping points
            if abs(slopeY) < 1e-8:
                outliers[incNext] = True
                continue
            if (slopeY * maxSlopeX > slopeX * maxSlopeY):
                maxSlopeX, maxSlopeY = slopeX, slopeY
                if np.linalg.norm(nextPoint - currPoint) <= search_radius_curr:
                    nextExtPoint = incNext
            
        # If a good point cannot be found, increase the search radius and try
        # again. The search radius is reset after a new point is found.
        if (nextExtPoint < x_sorted.shape[0]):
            if nextExtPoint == id:
                search_radius_curr *= 1.2
                continue
            if abs(maxSlopeY) > max_slope * abs(maxSlopeX):
                outliers[nextExtPoint] = 1
                search_radius_curr *= 1.2
                continue
            else:
                curvePoints.append(nextExtPoint)
                search_radius_curr = search_radius
        else:
            break
        id = nextExtPoint

    extX = x_sorted[curvePoints[1:]]
    extY = y_sorted[curvePoints[1:]]

    plt.figure()
    plt.plot(extX, extY)
    plt.show()

    # Second order moving least squares (fitting parabolas)
    extXNew, extYNew, extDY = movingLeastSquares(extX, extY)

    cubics = fitCubics(extXNew, extYNew, extDY)
    return extXNew, extYNew, cubics

def fitExtendedHenckyElasticity(scale, stress):
    press = (stress[:,0,0] + stress[:,1,1] + stress[:,2,2]) / 3
    henky = np.log(scale)
    logVol = henky.sum(axis=1)
    devHenky = henky - np.mean(henky, axis=1).reshape((-1, 1))
    devF2Henky = (devHenky * devHenky).sum(axis=1)
    devStress = np.array([s - np.eye(3)*p for s, p in zip(stress, press)])
    
    lMod = press / logVol
    lMod[-1] = 2 * lMod[-2] - lMod[-3]
    _, lMod, _ = movingLeastSquares(logVol, lMod, extent_frac=8, samples=logVol.size, clamp_left=True, clamp_right=True)
    lhs = np.zeros((lMod.size, lMod.size))
    for i in range(lMod.size):
        if i == 0:
            lhs[0, 0] = -logVol[0] / (logVol[1] - logVol[0])
            lhs[0, 1] = logVol[0] / (logVol[1] - logVol[0])
        elif i == lMod.size - 1:
            lhs[i, i - 1] = -logVol[i] / (logVol[i] - logVol[i - 1])
            lhs[i, i] = logVol[i] / (logVol[i] - logVol[i - 1])
        else:
            lhs[i, i - 1] = -logVol[i] / (logVol[i + 1] - logVol[i - 1])
            lhs[i, i + 1] = logVol[i] / (logVol[i + 1] - logVol[i - 1])
    np.fill_diagonal(lhs, lhs.diagonal() + 2)
    bMod = np.linalg.solve(lhs, lMod)
    bMod = np.maximum(bMod, 0)
    logVol, bMod, _ = movingLeastSquares(logVol, bMod, extent_frac=10, samples=logVol.size, clamp_left=True)
    bDeriv = np.zeros_like(bMod);
    for i in range(bMod.shape[0]):
        if i == 0:
            bDeriv[i] = (bMod[i+1] - bMod[i])\
            / (logVol[i+1] - logVol[i])
        # else:
        elif i == bMod.shape[0] - 1:
            bDeriv[i] = (bMod[i - 1] - bMod[i])\
            / (logVol[i - 1] - logVol[i])
        else:
            bDeriv[i] = (bMod[i+1] - bMod[i-1])\
            / (logVol[i+1] - logVol[i-1])
    
    sMod = (\
            devStress[:, 0, 0] / devHenky[:, 0]\
            + devStress[:, 1, 1] / devHenky[:, 1]\
            + devStress[:, 2, 2] / devHenky[:, 2]\
            ) / 6
    sMod[-1] = 2 * sMod[-2] - sMod[-3]

    devF2Henky, sMod, _ = movingLeastSquares(devF2Henky, sMod, extent_frac=8, samples=devF2Henky.size, clamp_left=True)
    lhs = np.zeros((sMod.size, sMod.size))
    for i in range(lMod.size):
        if i == 0:
            lhs[0, 0] = -devF2Henky[0] / (devF2Henky[1] - devF2Henky[0])
            lhs[0, 1] = devF2Henky[0] / (devF2Henky[1] - devF2Henky[0])
        elif i == lMod.size - 1:
        # else:
            lhs[i, i - 1] = -devF2Henky[i] / (devF2Henky[i] - devF2Henky[i - 1])
            lhs[i, i] = devF2Henky[i] / (devF2Henky[i] - devF2Henky[i - 1])
        else:
            lhs[i, i - 1] = -devF2Henky[i] / (devF2Henky[i + 1] - devF2Henky[i - 1])
            lhs[i, i + 1] = devF2Henky[i] / (devF2Henky[i + 1] - devF2Henky[i - 1])
    np.fill_diagonal(lhs, lhs.diagonal() + 1)
    mMod = np.linalg.solve(lhs, sMod)
    mMod = np.maximum(mMod, 0)
    
    _, mMod, _ = movingLeastSquares(devF2Henky, mMod, extent_frac=8, samples=devF2Henky.size, clamp_left=True)
    mDeriv = np.zeros_like(mMod)
    for i in range(mMod.shape[0]):
        if i == 0:
            mDeriv[i] = (mMod[i+1] - mMod[i])\
            / (devF2Henky[i+1] - devF2Henky[i])
        # else:
        elif i == mMod.shape[0] - 1:
            mDeriv[i] = (mMod[i - 1] - mMod[i])\
            / (devF2Henky[i - 1] - devF2Henky[i])
        else:
            mDeriv[i] = (mMod[i+1] - mMod[i-1])\
            / (devF2Henky[i+1] - devF2Henky[i-1])

    mCubic = fitCubics(devF2Henky, mMod, mDeriv)
    bCubic = fitCubics(logVol, bMod, bDeriv)

    return devF2Henky, mMod, mCubic, logVol, bMod, bCubic
    

def movingLeastSquares(_x, _y, samples = 100, extent_frac = 15, clamp_left=False, clamp_right=True):
    idx = np.argsort(_x);
    x = _x[idx]
    y = _y[idx]
    
    scaleX = abs(x.shape[0] / (x[-1] - x[0]))
    scaleY = abs(y.shape[0] / (y[-1] - y[0]))
    x *= scaleX
    y *= scaleY
    xNew = np.linspace(x[0], x[-1], samples, endpoint=True)
    yNew = np.zeros_like(xNew)
    dydx = np.zeros_like(xNew)

    extent_frac = 10;
    
    extent = abs(x[-1] - x[0]) / extent_frac;

    start = 1 if clamp_left else 0
    end = xNew.shape[0] - 1 if clamp_right else xNew.shape[0]
    for i in range(start, end):
        proxPoints = (x <= xNew[i] + extent) & (x >= xNew[i] - extent)
        extXDiff = x[proxPoints] - xNew[i]
        y_mean = y[proxPoints].mean()
        lhs = np.concatenate((
            (extXDiff * extXDiff).reshape((-1,1)),
            extXDiff.reshape(-1, 1),
            np.ones((proxPoints.sum(), 1))
            ), axis=1)
        rhs = y[proxPoints] - y_mean

        # The weight is 1 when extX[j] - extXNew[i] = 0, and 0 when
        # abs(extX[j] - extXNew[i]) = extent
        # w = extent / (np.abs(extX[proxPoints] - extXNew[i]) + extent) - 0.5
        w = extent / (np.abs(extXDiff) + extent) - 0.5
        
        # Use a inverse distance weight for the last point instead. This way
        # we can enforce extYNew[-1] = extY[-1] as a gradually stiffening soft
        # constraint.
        if clamp_left and (x[0] >= xNew[i] - extent):
            w[0] = extent / abs(x[0] - xNew[i]) - 1
        if (x[-1] <= xNew[i] + extent) and clamp_right:
            w[-1] = extent / abs(x[-1] - xNew[i]) - 1
        
        coeffs = np.linalg.solve(lhs.T @ (w.reshape((-1, 1)) * lhs), lhs.T @ (w * rhs))
        yNew[i] = coeffs[2] + y_mean
        dydx[i] = coeffs[1]
        
        if clamp_left and i == 1:
            dydx[0] = 2 * extXDiff[0] * coeffs[0] + coeffs[1]
        if clamp_right and (x[-1] <= xNew[i] + extent):
            dydx[-1] = 2 * extXDiff[-1] * coeffs[0] + coeffs[1]
    
    # Directly enforce extYNew[-1] = extY[-1]
    if clamp_left:
        yNew[0] = y[0]
    if clamp_right:
        yNew[-1] = y[-1]
    return xNew / scaleX, yNew / scaleY, dydx * scaleX / scaleY

def fitCubics(_x, _y, _dydx):
    scaleX = 1# (_x.shape[0] - 1) / (_x[-1] - _x[0])
    scaleY = 1#(_x.shape[0] - 1) / (_y[-1] - _y[0])
    x = scaleX * (_x - _x.mean())
    y = scaleY * (_y - _y.mean())
    dydx = _dydx * scaleY / scaleX
    # print(x, y, scaleY, dydx)
    cubics = np.zeros((x.shape[0] + 1, 3))
    for i in range(x.shape[0] - 1):
        x1 = x[i+1] - x[i]
        lhs = np.array([
            [x1, 1],
            [3 * x1 * x1, 2. * x1]
            ])
        rhs = np.array([
            (y[i+1] - y[i] - x1 * dydx[i]) / x1 / x1,
            (dydx[i+1] - dydx[i])])
        cubics[i, :2] = np.linalg.solve(lhs, rhs)
        cubics[i, 2] = dydx[i]
        
    cubics[-2, :] = [0, 0, dydx[-1]]
    cubics[-1, :] = [scaleX, scaleY, 0]
    return cubics
