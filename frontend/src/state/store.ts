import { create } from 'zustand';
import { Spline, SplinePoint } from '../types/Spline';

interface CompositorState {
  hasSource: boolean;
  frameCount: number;
  resolution: [number, number];
  currentFrame: number;
  activeTool: 'select' | 'pen' | 'hand';
  splines: Spline[];
  activeSplineId: string | null;
  currentSplinePoints: SplinePoint[];

  setHasSource: (has: boolean) => void;
  setFrameCount: (count: number) => void;
  setResolution: (res: [number, number]) => void;
  setCurrentFrame: (frame: number) => void;
  setActiveTool: (tool: 'select' | 'pen' | 'hand') => void;
  addPointToCurrentSpline: (point: SplinePoint) => void;
  finishCurrentSpline: () => Spline | null;
  clearCurrentSpline: () => void;
  setSplines: (splines: Spline[]) => void;
  addSpline: (spline: Spline) => void;
}

export const useStore = create<CompositorState>((set, get) => ({
  hasSource: false,
  frameCount: 0,
  resolution: [1920, 1080],
  currentFrame: 0,
  activeTool: 'pen',
  splines: [],
  activeSplineId: null,
  currentSplinePoints: [],

  setHasSource: (has) => set({ hasSource: has }),
  setFrameCount: (count) => set({ frameCount: count }),
  setResolution: (res) => set({ resolution: res }),
  setCurrentFrame: (frame) => set({ currentFrame: frame }),
  setActiveTool: (tool) => set({ activeTool: tool }),

  addPointToCurrentSpline: (point) => set((state) => ({
    currentSplinePoints: [...state.currentSplinePoints, point],
  })),

  finishCurrentSpline: () => {
    const state = get();
    if (state.currentSplinePoints.length < 2) {
      return null;
    }

    const spline: Spline = {
      id: `spline_${Date.now()}`,
      points: [...state.currentSplinePoints],
      closed: false,
    };

    set({
      splines: [...state.splines, spline],
      currentSplinePoints: [],
    });

    return spline;
  },

  clearCurrentSpline: () => set({ currentSplinePoints: [] }),
  setSplines: (splines) => set({ splines }),
  addSpline: (spline) => set((state) => ({ splines: [...state.splines, spline] })),
}));
