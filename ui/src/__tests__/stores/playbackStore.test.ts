/**
 * Playback Store Tests
 */
import { describe, it, expect, beforeEach, vi, afterEach } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { usePlaybackStore } from '@/stores/playbackStore';

describe('PlaybackStore', () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    vi.useFakeTimers();
  });

  afterEach(() => {
    vi.useRealTimers();
  });

  describe('initial state', () => {
    it('should start with playback stopped', () => {
      const store = usePlaybackStore();
      expect(store.isPlaying).toBe(false);
      expect(store.playbackRequestId).toBeNull();
    });

    it('should have loop enabled by default', () => {
      const store = usePlaybackStore();
      expect(store.loopPlayback).toBe(true);
    });
  });

  describe('play/stop', () => {
    it('should set isPlaying to true when play is called', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.play(30, 100, 0, onFrame);
      expect(store.isPlaying).toBe(true);
    });

    it('should set isPlaying to false when stop is called', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.play(30, 100, 0, onFrame);
      store.stop();
      expect(store.isPlaying).toBe(false);
    });

    it('should not start playback if already playing', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.play(30, 100, 0, onFrame);
      const firstRequestId = store.playbackRequestId;

      store.play(30, 100, 0, onFrame);
      expect(store.playbackRequestId).toBe(firstRequestId);
    });
  });

  describe('toggle', () => {
    it('should start playback when toggled from stopped', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.toggle(30, 100, 0, onFrame);
      expect(store.isPlaying).toBe(true);
    });

    it('should stop playback when toggled from playing', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.play(30, 100, 0, onFrame);
      store.toggle(30, 100, 0, onFrame);
      expect(store.isPlaying).toBe(false);
    });
  });

  describe('navigation', () => {
    it('goToStart should call onFrame with 0', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.goToStart(onFrame);
      expect(onFrame).toHaveBeenCalledWith(0);
    });

    it('goToEnd should call onFrame with last frame', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.goToEnd(100, onFrame);
      expect(onFrame).toHaveBeenCalledWith(99);
    });

    it('stepForward should increment frame', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.stepForward(50, 100, onFrame);
      expect(onFrame).toHaveBeenCalledWith(51);
    });

    it('stepForward should not exceed frame count', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.stepForward(99, 100, onFrame);
      expect(onFrame).toHaveBeenCalledWith(99);
    });

    it('stepBackward should decrement frame', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.stepBackward(50, onFrame);
      expect(onFrame).toHaveBeenCalledWith(49);
    });

    it('stepBackward should not go below 0', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.stepBackward(0, onFrame);
      expect(onFrame).toHaveBeenCalledWith(0);
    });

    it('goToFrame should clamp to valid range', () => {
      const store = usePlaybackStore();
      const onFrame = vi.fn();

      store.goToFrame(-10, 100, onFrame);
      expect(onFrame).toHaveBeenCalledWith(0);

      store.goToFrame(150, 100, onFrame);
      expect(onFrame).toHaveBeenCalledWith(99);

      store.goToFrame(50, 100, onFrame);
      expect(onFrame).toHaveBeenCalledWith(50);
    });
  });

  describe('loop setting', () => {
    it('should update loop playback setting', () => {
      const store = usePlaybackStore();

      store.setLoopPlayback(false);
      expect(store.loopPlayback).toBe(false);

      store.setLoopPlayback(true);
      expect(store.loopPlayback).toBe(true);
    });
  });
});
