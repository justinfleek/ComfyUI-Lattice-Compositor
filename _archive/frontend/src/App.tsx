import React, { useEffect } from 'react';
import Viewport from './viewport/Viewport';
import Timeline from './timeline/Timeline';
import ToolBar from './panels/ToolBar';
import LayerPanel from './panels/LayerPanel';
import { useStore } from './state/store';
import { getStatus, getSplines } from './bridge/api';

function App() {
  const {
    hasSource,
    setHasSource,
    setFrameCount,
    setResolution,
    setSplines,
  } = useStore();

  useEffect(() => {
    const checkStatus = async () => {
      try {
        const status = await getStatus();
        setHasSource(status.has_source);
        setFrameCount(status.frame_count);
        setResolution(status.resolution as [number, number]);

        if (status.has_source) {
          const splines = await getSplines();
          setSplines(splines);
        }
      } catch (err) {
        console.error('Status check failed:', err);
      }
    };

    checkStatus();
    const interval = setInterval(checkStatus, 2000);
    return () => clearInterval(interval);
  }, []);

  useEffect(() => {
    const handleKeyDown = (e: KeyboardEvent) => {
      const { setActiveTool, finishCurrentSpline } = useStore.getState();

      switch (e.key.toLowerCase()) {
        case 'v':
          setActiveTool('select');
          break;
        case 'p':
          setActiveTool('pen');
          break;
        case 'h':
          setActiveTool('hand');
          break;
        case 'enter':
          finishCurrentSpline();
          break;
        case 'escape':
          useStore.getState().clearCurrentSpline();
          break;
      }
    };

    window.addEventListener('keydown', handleKeyDown);
    return () => window.removeEventListener('keydown', handleKeyDown);
  }, []);

  const handleExport = () => {
    alert('Export ready! Run the WeylCompositorOutput node in ComfyUI to get your splines.');
  };

  return (
    <div className="app-container">
      <ToolBar />
      <div className="main-area">
        <div className="viewport-container">
          <Viewport />
        </div>
        <LayerPanel />
      </div>
      <Timeline />
      <div className="status-bar">
        <span>Status: {hasSource ? 'Source loaded' : 'Waiting for source'}</span>
        <span style={{ marginLeft: 'auto' }}>
          <button className="export-btn" onClick={handleExport}>
            Export to ComfyUI
          </button>
        </span>
      </div>
    </div>
  );
}

export default App;
