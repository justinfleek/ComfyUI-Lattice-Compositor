import React from 'react';
import { useStore } from '../state/store';

export default function ToolBar() {
  const { activeTool, setActiveTool } = useStore();

  return (
    <div className="toolbar">
      <button
        className={activeTool === 'select' ? 'active' : ''}
        onClick={() => setActiveTool('select')}
      >
        Select (V)
      </button>
      <button
        className={activeTool === 'pen' ? 'active' : ''}
        onClick={() => setActiveTool('pen')}
      >
        Pen (P)
      </button>
      <button
        className={activeTool === 'hand' ? 'active' : ''}
        onClick={() => setActiveTool('hand')}
      >
        Hand (H)
      </button>
    </div>
  );
}
