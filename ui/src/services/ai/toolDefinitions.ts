/**
 * AI Agent Tool Definitions
 *
 * These define all the actions the AI agent can take.
 * Each tool maps to a compositor store action.
 */

// ============================================================================
// TYPES
// ============================================================================

export interface ToolCall {
  id: string;
  name: string;
  arguments: Record<string, any>;
}

export interface ToolResult {
  toolCallId: string;
  success: boolean;
  result?: any;
  error?: string;
}

export interface ToolDefinition {
  type: 'function';
  function: {
    name: string;
    description: string;
    parameters: {
      type: 'object';
      properties: Record<string, any>;
      required?: string[];
    };
  };
}

// ============================================================================
// TOOL DEFINITIONS
// ============================================================================

export const TOOL_DEFINITIONS: ToolDefinition[] = [
  // ==========================================================================
  // LAYER MANAGEMENT
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'createLayer',
      description: 'Create a new layer in the composition. Returns the new layer ID.',
      parameters: {
        type: 'object',
        properties: {
          type: {
            type: 'string',
            enum: ['solid', 'text', 'shape', 'spline', 'particles', 'image', 'camera', 'control', 'nested'],
            description: 'The type of layer to create',
          },
          name: {
            type: 'string',
            description: 'Display name for the layer',
          },
          properties: {
            type: 'object',
            description: 'Initial properties for the layer (type-specific)',
          },
          position: {
            type: 'object',
            properties: {
              x: { type: 'number' },
              y: { type: 'number' },
            },
            description: 'Initial position',
          },
          inPoint: {
            type: 'number',
            description: 'Frame where layer appears (default: 0)',
          },
          outPoint: {
            type: 'number',
            description: 'Frame where layer disappears (default: composition duration)',
          },
        },
        required: ['type'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'deleteLayer',
      description: 'Delete a layer from the composition',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer to delete',
          },
        },
        required: ['layerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'duplicateLayer',
      description: 'Create a copy of an existing layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer to duplicate',
          },
          newName: {
            type: 'string',
            description: 'Name for the duplicated layer',
          },
        },
        required: ['layerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'renameLayer',
      description: 'Change the display name of a layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer to rename',
          },
          name: {
            type: 'string',
            description: 'New name for the layer',
          },
        },
        required: ['layerId', 'name'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'setLayerParent',
      description: 'Set a layer\'s parent (for hierarchical transforms)',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the child layer',
          },
          parentId: {
            type: 'string',
            description: 'ID of the parent layer (null to unparent)',
            nullable: true,
          },
        },
        required: ['layerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'reorderLayers',
      description: 'Change the stacking order of layers',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer to move',
          },
          newIndex: {
            type: 'number',
            description: 'New index in the layer stack (0 = top)',
          },
        },
        required: ['layerId', 'newIndex'],
      },
    },
  },

  // ==========================================================================
  // PROPERTY MODIFICATION
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'setLayerProperty',
      description: 'Set a property value on a layer (non-animated)',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          propertyPath: {
            type: 'string',
            description: 'Dot-notation path to property (e.g., "position.x", "opacity", "text")',
          },
          value: {
            description: 'Value to set (type depends on property)',
          },
        },
        required: ['layerId', 'propertyPath', 'value'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'setLayerTransform',
      description: 'Set multiple transform properties at once',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          position: {
            type: 'object',
            properties: { x: { type: 'number' }, y: { type: 'number' } },
          },
          scale: {
            type: 'object',
            properties: { x: { type: 'number' }, y: { type: 'number' } },
          },
          rotation: {
            type: 'number',
            description: 'Rotation in degrees',
          },
          opacity: {
            type: 'number',
            description: 'Opacity 0-100',
          },
          anchorPoint: {
            type: 'object',
            properties: { x: { type: 'number' }, y: { type: 'number' } },
          },
        },
        required: ['layerId'],
      },
    },
  },

  // ==========================================================================
  // KEYFRAME ANIMATION
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'addKeyframe',
      description: 'Add a keyframe to animate a property',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          propertyPath: {
            type: 'string',
            description: 'Property to animate (e.g., "position", "opacity", "scale")',
          },
          frame: {
            type: 'number',
            description: 'Frame number (0-80)',
          },
          value: {
            description: 'Value at this keyframe',
          },
          interpolation: {
            type: 'string',
            enum: ['linear', 'bezier', 'hold', 'easeIn', 'easeOut', 'easeInOut',
                   'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
                   'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
                   'easeInElastic', 'easeOutElastic', 'easeOutBounce'],
            description: 'Interpolation type (default: linear)',
          },
        },
        required: ['layerId', 'propertyPath', 'frame', 'value'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'removeKeyframe',
      description: 'Remove a keyframe from a property',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          propertyPath: {
            type: 'string',
            description: 'Property path',
          },
          frame: {
            type: 'number',
            description: 'Frame number of keyframe to remove',
          },
        },
        required: ['layerId', 'propertyPath', 'frame'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'setKeyframeEasing',
      description: 'Change the interpolation of an existing keyframe',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          propertyPath: {
            type: 'string',
            description: 'Property path',
          },
          frame: {
            type: 'number',
            description: 'Frame number of keyframe',
          },
          interpolation: {
            type: 'string',
            description: 'New interpolation type',
          },
        },
        required: ['layerId', 'propertyPath', 'frame', 'interpolation'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'scaleKeyframeTiming',
      description: 'Scale all keyframes on a layer to speed up or slow down animation',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          scaleFactor: {
            type: 'number',
            description: 'Scale factor (0.5 = 2x faster, 2.0 = 2x slower)',
          },
          propertyPath: {
            type: 'string',
            description: 'Specific property to scale (omit for all properties)',
          },
        },
        required: ['layerId', 'scaleFactor'],
      },
    },
  },

  // ==========================================================================
  // EXPRESSIONS
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'setExpression',
      description: 'Apply an expression to a property for dynamic animation',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          propertyPath: {
            type: 'string',
            description: 'Property to apply expression to',
          },
          expressionType: {
            type: 'string',
            enum: ['jitter', 'repeatAfter', 'repeatBefore', 'inertia', 'bounce', 'elastic'],
            description: 'Type of expression',
          },
          params: {
            type: 'object',
            description: 'Expression parameters (varies by type)',
          },
        },
        required: ['layerId', 'propertyPath', 'expressionType'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'removeExpression',
      description: 'Remove an expression from a property',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          propertyPath: {
            type: 'string',
            description: 'Property to remove expression from',
          },
        },
        required: ['layerId', 'propertyPath'],
      },
    },
  },

  // ==========================================================================
  // EFFECTS
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'addEffect',
      description: 'Add an effect to a layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          effectType: {
            type: 'string',
            enum: ['gaussianBlur', 'motionBlur', 'radialBlur', 'zoomBlur',
                   'brightnessContrast', 'hueSaturation', 'colorBalance', 'tint',
                   'glow', 'dropShadow', 'stroke',
                   'bulge', 'twirl', 'wave', 'displacement',
                   'gradient', 'fractalNoise', 'checkerboard'],
            description: 'Type of effect',
          },
          params: {
            type: 'object',
            description: 'Effect parameters',
          },
        },
        required: ['layerId', 'effectType'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'updateEffect',
      description: 'Update parameters of an existing effect',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          effectId: {
            type: 'string',
            description: 'ID of the effect',
          },
          params: {
            type: 'object',
            description: 'Parameters to update',
          },
        },
        required: ['layerId', 'effectId', 'params'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'removeEffect',
      description: 'Remove an effect from a layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          effectId: {
            type: 'string',
            description: 'ID of the effect to remove',
          },
        },
        required: ['layerId', 'effectId'],
      },
    },
  },

  // ==========================================================================
  // PARTICLE SYSTEM
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'configureParticles',
      description: 'Configure a particle layer\'s emission and behavior',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the particle layer',
          },
          emitter: {
            type: 'object',
            properties: {
              type: { type: 'string', enum: ['point', 'line', 'box', 'circle', 'path'] },
              position: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } } },
              size: { type: 'object', properties: { width: { type: 'number' }, height: { type: 'number' } } },
              pathReference: { type: 'string' },
            },
          },
          particles: {
            type: 'object',
            properties: {
              count: { type: 'number' },
              lifetime: { type: 'object', properties: { min: { type: 'number' }, max: { type: 'number' } } },
              speed: { type: 'object', properties: { min: { type: 'number' }, max: { type: 'number' } } },
              direction: { type: 'object', properties: { min: { type: 'number' }, max: { type: 'number' } } },
              size: { type: 'object', properties: { start: { type: 'number' }, end: { type: 'number' } } },
              opacity: { type: 'object', properties: { start: { type: 'number' }, end: { type: 'number' } } },
              color: { type: 'object' },
              rotation: { type: 'object', properties: { initial: { type: 'number' }, speed: { type: 'number' } } },
            },
          },
          physics: {
            type: 'object',
            properties: {
              gravity: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } } },
              wind: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } } },
              turbulence: { type: 'object', properties: { strength: { type: 'number' }, scale: { type: 'number' } } },
            },
          },
        },
        required: ['layerId'],
      },
    },
  },

  // ==========================================================================
  // CAMERA SYSTEM
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'applyCameraTrajectory',
      description: 'Apply a predefined camera trajectory/motion preset to a camera layer. Creates smooth animated camera movements like orbit, dolly, crane, and more.',
      parameters: {
        type: 'object',
        properties: {
          cameraLayerId: {
            type: 'string',
            description: 'ID of the camera layer to apply trajectory to',
          },
          trajectoryType: {
            type: 'string',
            enum: [
              'orbit', 'orbit_reverse', 'swing1', 'swing2',
              'dolly_in', 'dolly_out', 'pan_left', 'pan_right',
              'tilt_up', 'tilt_down', 'zoom_in', 'zoom_out',
              'circle', 'figure8', 'spiral_in', 'spiral_out',
              'crane_up', 'crane_down', 'truck_left', 'truck_right',
              'arc_left', 'arc_right',
            ],
            description: 'Type of camera trajectory preset',
          },
          startFrame: {
            type: 'number',
            description: 'Frame to start the trajectory (default: 0)',
          },
          duration: {
            type: 'number',
            description: 'Duration in frames (default: composition length)',
          },
          amplitude: {
            type: 'number',
            description: 'Strength multiplier for the motion (default: 1.0)',
          },
          loops: {
            type: 'number',
            description: 'Number of complete cycles for orbits/circles (default: 1)',
          },
          easing: {
            type: 'string',
            enum: ['linear', 'ease-in', 'ease-out', 'ease-in-out', 'bounce'],
            description: 'Easing type for the motion (default: ease-in-out)',
          },
          center: {
            type: 'object',
            properties: {
              x: { type: 'number' },
              y: { type: 'number' },
              z: { type: 'number' },
            },
            description: 'Center point for orbit/swing trajectories (default: composition center)',
          },
        },
        required: ['cameraLayerId', 'trajectoryType'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'addCameraShake',
      description: 'Add camera shake effect for handheld, impact, or earthquake simulation',
      parameters: {
        type: 'object',
        properties: {
          cameraLayerId: {
            type: 'string',
            description: 'ID of the camera layer',
          },
          shakeType: {
            type: 'string',
            enum: ['handheld', 'impact', 'earthquake', 'subtle'],
            description: 'Type of camera shake preset',
          },
          intensity: {
            type: 'number',
            description: 'Shake intensity 0-1 (default: varies by type)',
          },
          frequency: {
            type: 'number',
            description: 'Shake frequency multiplier (default: 1.0)',
          },
          startFrame: {
            type: 'number',
            description: 'Frame to start shake (default: 0)',
          },
          duration: {
            type: 'number',
            description: 'Duration in frames (default: entire composition)',
          },
          decay: {
            type: 'number',
            description: 'Shake decay 0-1, higher = more decay over time (default: 0)',
          },
          rotationEnabled: {
            type: 'boolean',
            description: 'Enable rotation shake (default: true for most types)',
          },
          seed: {
            type: 'number',
            description: 'Random seed for deterministic shake (default: random)',
          },
        },
        required: ['cameraLayerId', 'shakeType'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'applyRackFocus',
      description: 'Create a rack focus effect - smooth focus transition between two distances. Used for shifting audience attention between foreground and background.',
      parameters: {
        type: 'object',
        properties: {
          cameraLayerId: {
            type: 'string',
            description: 'ID of the camera layer',
          },
          startDistance: {
            type: 'number',
            description: 'Starting focus distance in pixels',
          },
          endDistance: {
            type: 'number',
            description: 'Ending focus distance in pixels',
          },
          startFrame: {
            type: 'number',
            description: 'Frame to start the rack focus (default: 0)',
          },
          duration: {
            type: 'number',
            description: 'Duration of the focus transition in frames (default: 30)',
          },
          easing: {
            type: 'string',
            enum: ['linear', 'ease-in', 'ease-out', 'ease-in-out', 'snap'],
            description: 'Easing type for focus transition (default: ease-in-out)',
          },
          holdStart: {
            type: 'number',
            description: 'Frames to hold at start focus before transitioning (default: 0)',
          },
          holdEnd: {
            type: 'number',
            description: 'Frames to hold at end focus after transitioning (default: 0)',
          },
        },
        required: ['cameraLayerId', 'startDistance', 'endDistance'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'setCameraPathFollowing',
      description: 'Make a camera follow a spline path. The camera will move along the path and optionally look at a target or along the path tangent.',
      parameters: {
        type: 'object',
        properties: {
          cameraLayerId: {
            type: 'string',
            description: 'ID of the camera layer',
          },
          splineLayerId: {
            type: 'string',
            description: 'ID of the spline layer to follow (null to disable)',
            nullable: true,
          },
          lookMode: {
            type: 'string',
            enum: ['tangent', 'target', 'fixed'],
            description: 'How the camera should orient: tangent (look along path), target (look at specific point), fixed (maintain direction)',
          },
          lookTarget: {
            type: 'object',
            properties: {
              x: { type: 'number' },
              y: { type: 'number' },
              z: { type: 'number' },
            },
            description: 'Point to look at when lookMode is "target"',
          },
          startOffset: {
            type: 'number',
            description: 'Starting position along path 0-1 (default: 0)',
          },
          speed: {
            type: 'number',
            description: 'Speed multiplier for path traversal (default: 1.0)',
          },
          bankAmount: {
            type: 'number',
            description: 'Amount of banking/roll on curves 0-1 (default: 0)',
          },
          smoothing: {
            type: 'number',
            description: 'Path smoothing amount 0-1 (default: 0.5)',
          },
        },
        required: ['cameraLayerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'setCameraAutoFocus',
      description: 'Enable depth-aware autofocus on a camera. The camera will automatically adjust focus based on depth map.',
      parameters: {
        type: 'object',
        properties: {
          cameraLayerId: {
            type: 'string',
            description: 'ID of the camera layer',
          },
          enabled: {
            type: 'boolean',
            description: 'Enable or disable autofocus',
          },
          mode: {
            type: 'string',
            enum: ['center', 'point', 'nearest', 'farthest'],
            description: 'Autofocus mode: center (center of frame), point (specific point), nearest/farthest (extreme depth)',
          },
          focusPoint: {
            type: 'object',
            properties: {
              x: { type: 'number', description: 'X position 0-1' },
              y: { type: 'number', description: 'Y position 0-1' },
            },
            description: 'Focus point when mode is "point" (normalized 0-1)',
          },
          smoothing: {
            type: 'number',
            description: 'Focus smoothing 0-1, higher = smoother transitions (default: 0.8)',
          },
        },
        required: ['cameraLayerId'],
      },
    },
  },

  // ==========================================================================
  // TEXT SPECIFIC
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'setTextContent',
      description: 'Set the text content and styling of a text layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the text layer',
          },
          text: {
            type: 'string',
            description: 'Text content',
          },
          fontSize: {
            type: 'number',
            description: 'Font size in pixels',
          },
          fontFamily: {
            type: 'string',
            description: 'Font family name',
          },
          fontWeight: {
            type: 'number',
            description: 'Font weight (100-900)',
          },
          color: {
            type: 'object',
            properties: { r: { type: 'number' }, g: { type: 'number' }, b: { type: 'number' }, a: { type: 'number' } },
          },
          alignment: {
            type: 'string',
            enum: ['left', 'center', 'right'],
          },
        },
        required: ['layerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'setTextPath',
      description: 'Attach text to follow a spline path',
      parameters: {
        type: 'object',
        properties: {
          textLayerId: {
            type: 'string',
            description: 'ID of the text layer',
          },
          splineLayerId: {
            type: 'string',
            description: 'ID of the spline layer to follow (null to detach)',
            nullable: true,
          },
          startOffset: {
            type: 'number',
            description: 'Starting position along path (0-1)',
          },
        },
        required: ['textLayerId'],
      },
    },
  },

  // ==========================================================================
  // SPLINE/PATH
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'setSplinePoints',
      description: 'Set the control points of a spline layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the spline layer',
          },
          points: {
            type: 'array',
            items: {
              type: 'object',
              properties: {
                x: { type: 'number' },
                y: { type: 'number' },
                handleIn: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } }, nullable: true },
                handleOut: { type: 'object', properties: { x: { type: 'number' }, y: { type: 'number' } }, nullable: true },
              },
            },
            description: 'Array of control points',
          },
          closed: {
            type: 'boolean',
            description: 'Whether the path is closed',
          },
        },
        required: ['layerId', 'points'],
      },
    },
  },

  // ==========================================================================
  // TIME REMAPPING
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'setTimeRemap',
      description: 'Enable time remapping on a layer to control playback speed',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
          enabled: {
            type: 'boolean',
            description: 'Enable or disable time remapping',
          },
          keyframes: {
            type: 'array',
            items: {
              type: 'object',
              properties: {
                frame: { type: 'number', description: 'Output frame' },
                value: { type: 'number', description: 'Source frame to show' },
                interpolation: { type: 'string' },
              },
            },
            description: 'Time remap keyframes',
          },
        },
        required: ['layerId'],
      },
    },
  },

  // ==========================================================================
  // PLAYBACK CONTROL
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'setCurrentFrame',
      description: 'Jump to a specific frame',
      parameters: {
        type: 'object',
        properties: {
          frame: {
            type: 'number',
            description: 'Frame number (0-80)',
          },
        },
        required: ['frame'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'playPreview',
      description: 'Start or stop playback preview',
      parameters: {
        type: 'object',
        properties: {
          play: {
            type: 'boolean',
            description: 'True to play, false to stop',
          },
        },
        required: ['play'],
      },
    },
  },

  // ==========================================================================
  // AI IMAGE PROCESSING
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'decomposeImage',
      description: 'Use AI to decompose an image into multiple RGBA layers (requires Qwen-Image-Layered model). Creates separate image layers for background, foreground, and intermediate elements.',
      parameters: {
        type: 'object',
        properties: {
          sourceLayerId: {
            type: 'string',
            description: 'ID of the image layer to decompose',
          },
          numLayers: {
            type: 'number',
            description: 'Number of layers to generate (3-16, default 4)',
            minimum: 3,
            maximum: 16,
          },
        },
        required: ['sourceLayerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'vectorizeImage',
      description: 'Convert an image layer to vector spline paths. Creates one or more SplineLayer(s) with keyframeable control points that can be animated individually, by group, or as a whole layer. Ideal for logos, icons, and graphics.',
      parameters: {
        type: 'object',
        properties: {
          sourceLayerId: {
            type: 'string',
            description: 'ID of the image layer to vectorize',
          },
          mode: {
            type: 'string',
            enum: ['trace', 'ai'],
            description: 'Vectorization mode: "trace" (VTracer, fast, works on any image) or "ai" (StarVector, best for icons/logos)',
          },
          separateLayers: {
            type: 'boolean',
            description: 'Create separate layer for each path (default: true)',
          },
          groupByPath: {
            type: 'boolean',
            description: 'Assign group IDs to control points for group animation (default: true)',
          },
          autoGroupByRegion: {
            type: 'boolean',
            description: 'Auto-group points by quadrant region (default: false)',
          },
          enableAnimation: {
            type: 'boolean',
            description: 'Enable keyframe animation on created layers (default: true)',
          },
          traceOptions: {
            type: 'object',
            description: 'VTracer-specific options (only used if mode is "trace")',
            properties: {
              colorMode: {
                type: 'string',
                enum: ['color', 'binary'],
                description: 'Color mode: "color" for full color, "binary" for black & white',
              },
              filterSpeckle: {
                type: 'number',
                description: 'Filter speckle size (0-100, default 4)',
              },
              cornerThreshold: {
                type: 'number',
                description: 'Corner threshold in degrees (0-180, default 60)',
              },
              colorPrecision: {
                type: 'number',
                description: 'Color precision (1-10, default 6)',
              },
              layerDifference: {
                type: 'number',
                description: 'Layer difference threshold (1-256, default 16)',
              },
            },
          },
        },
        required: ['sourceLayerId'],
      },
    },
  },

  // ==========================================================================
  // UTILITY
  // ==========================================================================
  {
    type: 'function',
    function: {
      name: 'getLayerInfo',
      description: 'Get detailed information about a layer',
      parameters: {
        type: 'object',
        properties: {
          layerId: {
            type: 'string',
            description: 'ID of the layer',
          },
        },
        required: ['layerId'],
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'findLayers',
      description: 'Find layers by name or type',
      parameters: {
        type: 'object',
        properties: {
          name: {
            type: 'string',
            description: 'Layer name to search for (partial match)',
          },
          type: {
            type: 'string',
            description: 'Layer type to filter by',
          },
        },
      },
    },
  },
  {
    type: 'function',
    function: {
      name: 'getProjectState',
      description: 'Get a summary of the current project state',
      parameters: {
        type: 'object',
        properties: {},
      },
    },
  },
];
