import React from 'react';
import { useStore } from '../state/store';

export default function Timeline() {
  const { frameCount, currentFrame, setCurrentFrame } = useStore();

  const handleRulerClick = (e: React.MouseEvent<HTMLDivElement>) => {
    const rect = e.currentTarget.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const percent = x / rect.width;
    const frame = Math.round(percent * Math.max(1, frameCount - 1));
    setCurrentFrame(frame);
  };

  const playheadPosition = frameCount > 1
    ? (currentFrame / (frameCount - 1)) * 100
    : 0;

  return (
    <div className="timeline">
      <div className="timeline-header">
        <span>Timeline</span>
        <span>Frame: {currentFrame} / {frameCount}</span>
      </div>
      <div className="timeline-ruler" onClick={handleRulerClick}>
        <div
          className="playhead"
          style={{ left: `${playheadPosition}%` }}
        />
      </div>
    </div>
  );
}
