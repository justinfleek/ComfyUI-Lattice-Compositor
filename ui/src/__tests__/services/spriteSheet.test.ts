/**
 * Sprite Sheet Service Tests
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { SpriteSheetService } from '@/services/spriteSheet';

describe('SpriteSheetService', () => {
  let service: SpriteSheetService;

  beforeEach(() => {
    service = new SpriteSheetService();
  });

  describe('createFromTexture', () => {
    it('should create sprite sheet config from texture dimensions', () => {
      // Create a mock texture with image dimensions
      const mockTexture = {
        image: { width: 256, height: 128 },
      } as any;

      const config = service.createFromTexture(mockTexture, 4, 2, {
        name: 'test-sheet',
        frameRate: 24,
      });

      expect(config).toBeDefined();
      expect(config.name).toBe('test-sheet');
      expect(config.columns).toBe(4);
      expect(config.rows).toBe(2);
      expect(config.totalFrames).toBe(8);
      expect(config.frameWidth).toBe(64);  // 256 / 4
      expect(config.frameHeight).toBe(64); // 128 / 2
      expect(config.defaultFrameRate).toBe(24);
    });

    it('should generate correct UV coordinates for each frame', () => {
      const mockTexture = {
        image: { width: 100, height: 100 },
      } as any;

      const config = service.createFromTexture(mockTexture, 2, 2);

      expect(config.frames.length).toBe(4);

      // First frame (top-left in image = bottom-left in UV)
      expect(config.frames[0].uv.u).toBe(0);
      expect(config.frames[0].uv.v).toBe(0.5); // Flipped Y

      // Second frame (top-right)
      expect(config.frames[1].uv.u).toBe(0.5);
      expect(config.frames[1].uv.v).toBe(0.5);

      // Third frame (bottom-left)
      expect(config.frames[2].uv.u).toBe(0);
      expect(config.frames[2].uv.v).toBe(0);

      // Fourth frame (bottom-right)
      expect(config.frames[3].uv.u).toBe(0.5);
      expect(config.frames[3].uv.v).toBe(0);
    });

    it('should create default "all" animation', () => {
      const mockTexture = {
        image: { width: 100, height: 50 },
      } as any;

      const config = service.createFromTexture(mockTexture, 4, 2);

      expect(config.animations.has('all')).toBe(true);
      const allAnim = config.animations.get('all')!;
      expect(allAnim.frames.length).toBe(8);
      expect(allAnim.frames).toEqual([0, 1, 2, 3, 4, 5, 6, 7]);
    });
  });

  describe('addAnimation', () => {
    it('should add custom animation sequence', () => {
      const mockTexture = {
        image: { width: 160, height: 32 },
      } as any;

      const config = service.createFromTexture(mockTexture, 5, 1, { id: 'anim-test' });

      service.addAnimation('anim-test', {
        name: 'walk',
        frames: [0, 1, 2, 3, 2, 1],
        frameRate: 12,
        loop: true,
        pingPong: false,
      });

      const sheet = service.getSheet('anim-test');
      expect(sheet?.animations.has('walk')).toBe(true);
      expect(sheet?.animations.get('walk')?.frames).toEqual([0, 1, 2, 3, 2, 1]);
    });
  });

  describe('getFrameAtTime', () => {
    it('should return correct frame for time', () => {
      const mockTexture = {
        image: { width: 120, height: 30 },
      } as any;

      const config = service.createFromTexture(mockTexture, 4, 1, {
        id: 'time-test',
        frameRate: 10, // 100ms per frame
      });

      // At 0ms, should be frame 0
      expect(service.getFrameAtTime('time-test', 'all', 0)).toBe(0);

      // At 150ms, should be frame 1
      expect(service.getFrameAtTime('time-test', 'all', 150)).toBe(1);

      // At 350ms, should be frame 3
      expect(service.getFrameAtTime('time-test', 'all', 350)).toBe(3);
    });

    it('should loop animation correctly', () => {
      const mockTexture = {
        image: { width: 100, height: 50 },
      } as any;

      const config = service.createFromTexture(mockTexture, 2, 1, {
        id: 'loop-test',
        frameRate: 10, // 100ms per frame, total 200ms
        loop: true,
      });

      // After one full cycle (200ms), should loop back to frame 0
      expect(service.getFrameAtTime('loop-test', 'all', 200)).toBe(0);
      expect(service.getFrameAtTime('loop-test', 'all', 300)).toBe(1);
    });
  });

  describe('getFrameUV', () => {
    it('should return correct UV for frame index', () => {
      const mockTexture = {
        image: { width: 100, height: 100 },
      } as any;

      const config = service.createFromTexture(mockTexture, 2, 2, { id: 'uv-test' });

      const uv = service.getFrameUV('uv-test', 0);
      expect(uv).toBeDefined();
      expect(uv?.u).toBe(0);
      expect(uv?.w).toBe(0.5);
      expect(uv?.h).toBe(0.5);
    });

    it('should return null for invalid frame', () => {
      const mockTexture = {
        image: { width: 100, height: 100 },
      } as any;

      service.createFromTexture(mockTexture, 2, 2, { id: 'invalid-test' });

      expect(service.getFrameUV('invalid-test', 99)).toBeNull();
      expect(service.getFrameUV('non-existent', 0)).toBeNull();
    });
  });

  describe('getParticleTextureConfig', () => {
    it('should return config compatible with GPU particle system', () => {
      const mockTexture = {
        image: { width: 256, height: 64 },
      } as any;

      const config = service.createFromTexture(mockTexture, 8, 2, {
        id: 'particle-test',
        frameRate: 30,
      });
      config.url = 'test.png';

      const particleConfig = service.getParticleTextureConfig('particle-test');

      expect(particleConfig).toBeDefined();
      expect(particleConfig?.spriteSheetColumns).toBe(8);
      expect(particleConfig?.spriteSheetRows).toBe(2);
      expect(particleConfig?.animateSprite).toBe(true);
      expect(particleConfig?.spriteFrameRate).toBe(30);
    });
  });

  describe('cleanup', () => {
    it('should remove sheet and its resources', () => {
      const mockTexture = {
        image: { width: 100, height: 100 },
        dispose: () => {},
      } as any;

      service.createFromTexture(mockTexture, 2, 2, { id: 'remove-test' });

      expect(service.hasSheet('remove-test')).toBe(true);
      service.removeSheet('remove-test');
      expect(service.hasSheet('remove-test')).toBe(false);
    });

    it('should dispose all resources', () => {
      const mockTexture1 = { image: { width: 100, height: 100 }, dispose: () => {} } as any;
      const mockTexture2 = { image: { width: 100, height: 100 }, dispose: () => {} } as any;

      service.createFromTexture(mockTexture1, 2, 2, { id: 'dispose-1' });
      service.createFromTexture(mockTexture2, 2, 2, { id: 'dispose-2' });

      expect(service.getAllSheets().length).toBe(2);
      service.dispose();
      expect(service.getAllSheets().length).toBe(0);
    });
  });
});
