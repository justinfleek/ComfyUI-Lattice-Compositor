import data_input
import data_fitting
import data_vis
import data_save
import sys
import matplotlib.pyplot as plt

results = data_input.averageExperiments(
        data_input.importExperiments(sys.argv[1:])
        )

scale, stresses = data_fitting.extractPressStresses(results)

devVol, mMod, mDeriv, logVol, bMod, bDeriv = data_fitting.fitExtendedHenckyElasticity(scale, stresses)
data_vis.plotElastic(results[0]["stress"], results[0]["scale"], results[0]["std"])

data_save.saveElasticity("test_elastic.txt", devVol, mMod, mDeriv,\
        logVol, bMod, bDeriv)

plt.show()

