import React from 'react';
import { useStore } from '../state/store';
import { addSpline as apiAddSpline, clearSplines } from '../bridge/api';

export default function LayerPanel() {
  const {
    splines,
    currentSplinePoints,
    finishCurrentSpline,
    clearCurrentSpline,
  } = useStore();

  const handleFinishSpline = async () => {
    const spline = finishCurrentSpline();
    if (spline) {
      await apiAddSpline(spline);
    }
  };

  const handleClearAll = async () => {
    await clearSplines();
    useStore.getState().setSplines([]);
  };

  return (
    <div className="sidebar">
      <h3>Tools</h3>
      {currentSplinePoints.length > 0 && (
        <div style={{ marginBottom: 16 }}>
          <p style={{ fontSize: 12, marginBottom: 8 }}>
            Drawing: {currentSplinePoints.length} points
          </p>
          <button onClick={handleFinishSpline} style={{ marginRight: 8 }}>
            Finish Spline
          </button>
          <button onClick={clearCurrentSpline}>
            Cancel
          </button>
        </div>
      )}

      <h3>Splines ({splines.length})</h3>
      <div className="spline-list">
        {splines.map((spline, i) => (
          <div key={spline.id} className="spline-item">
            Spline {i + 1}: {spline.points.length} points
          </div>
        ))}
      </div>

      {splines.length > 0 && (
        <button onClick={handleClearAll} style={{ marginTop: 16 }}>
          Clear All Splines
        </button>
      )}
    </div>
  );
}
