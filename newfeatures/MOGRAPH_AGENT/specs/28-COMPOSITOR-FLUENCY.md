# Specification 28: Compositor Fluency
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-28  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Proprietary Core IP  

---

## 1. Overview

This specification teaches the AI to think like a **senior motion graphics artist** who has spent 10,000+ hours in After Effects, Fusion, and similar compositors. The AI must understand:

1. **Layer Architecture** - How compositions are built from layers
2. **Z-Space & 3D** - Spatial relationships in simulated 3D
3. **Keyframe Mechanics** - The atomic unit of animation
4. **Expressions & Automation** - Programmatic animation control
5. **Nested Compositions** - Modular animation design
6. **Render Pipeline** - How frames are calculated

The AI doesn't just know WHAT to animate - it knows exactly HOW to construct the animation layer by layer, keyframe by keyframe.

---

## 2. Layer Architecture

### 2.1 Layer Mental Model

```yaml
layer_fundamentals:
  definition: >
    A layer is a discrete visual element with its own transform stack,
    timeline, effects, and blending mode. Layers stack vertically in
    the timeline, with higher layers rendered on top of lower layers
    (unless 3D ordering or blend modes change this).

  layer_types:
    solid:
      description: "Rectangle of solid color"
      use_cases: ["Background", "Color overlay", "Matte"]
      animatable: ["Position", "Scale", "Rotation", "Opacity", "Color"]
      
    shape:
      description: "Vector paths with fill/stroke"
      use_cases: ["Graphics", "Icons", "Animated shapes", "Masks"]
      animatable: ["Path", "Fill", "Stroke", "Transform"]
      sublayers: true  # Contains groups within
      
    text:
      description: "Typography with per-character control"
      use_cases: ["Titles", "Captions", "Kinetic typography"]
      animatable: ["Source text", "Per-character position/scale/rotation/opacity"]
      special: "Text animators for range-based animation"
      
    image:
      description: "Raster image source"
      use_cases: ["Photos", "Product images", "Backgrounds"]
      animatable: ["Transform", "Effects"]
      
    video:
      description: "Moving image sequence"
      use_cases: ["Footage", "Pre-rendered elements"]
      animatable: ["Transform", "Effects", "Time remapping"]
      
    null_object:
      description: "Invisible layer for control"
      use_cases: ["Parent for multiple layers", "Expression control", "Camera target"]
      critical_knowledge: "NULL LAYERS ARE THE SECRET WEAPON OF COMPOSITORS"
      
    adjustment:
      description: "Applies effects to all layers below"
      use_cases: ["Global color correction", "Blur zones", "Style treatments"]
      
    camera:
      description: "Virtual camera for 3D scenes"
      use_cases: ["Parallax", "Depth", "Camera movements"]
      properties: ["Position", "Point of Interest", "Zoom", "Depth of Field"]
      
    light:
      description: "Light source for 3D layers"
      use_cases: ["Dramatic lighting", "Shadows", "Material response"]

  layer_properties:
    transform_stack:
      order: ["Anchor Point", "Position", "Scale", "Rotation", "Opacity"]
      critical: "ANCHOR POINT AFFECTS ALL OTHER TRANSFORMS"
      
    anchor_point:
      description: "The pivot point for all transforms"
      default: "Center of layer content"
      adjustment: "Move anchor without moving layer: Pan Behind tool"
      importance: >
        Setting correct anchor point is CRITICAL for natural motion.
        Rotate a door? Anchor at hinge. Scale a button? Anchor at center.
        Logo wipe? Anchor at reveal edge.
        
    position:
      description: "Layer location in composition"
      coordinate_system: "Origin at comp top-left"
      3d_mode: "Adds Z dimension"
      expressions_common: ["wiggle()", "loopOut()", "valueAtTime()"]
      
    scale:
      description: "Size multiplier"
      constraint: "0% to unlimited"
      negative_values: "Flips layer (horizontal/vertical)"
      link_dimensions: "Lock aspect ratio by default"
      
    rotation:
      description: "Degrees of rotation"
      z_rotation: "2D default"
      3d_mode: "Adds X/Y rotation (pitch/yaw)"
      full_rotations: "Can be >360° for multiple spins"
      
    opacity:
      description: "Transparency"
      constraint: "0-100%"
      vs_effects: "Opacity is compositing-time; effect opacity varies"
```

### 2.2 Layer Stacking Logic

```haskell
-- | The compositor must understand layer ordering deeply
data LayerStack = LayerStack
  { lsLayers :: ![Layer]          -- Ordered bottom to top
  , lsBlendingMode :: !BlendMode
  , ls3DEnabled :: !Bool
  } deriving (Eq, Show, Generic)

-- | Render order determination
data RenderOrder
  = RO2DStack            -- Simple top-to-bottom (top renders last, on top)
  | RO3DByZDepth         -- 3D layers sorted by Z position
  | RO3DInterleaved      -- Mix of 2D stacking and 3D depth
  deriving (Eq, Show, Enum, Bounded)

-- | Determine how layers composite
determineRenderOrder :: LayerStack -> [(Layer, Int)]
determineRenderOrder stack
  | not (ls3DEnabled stack) = 
      -- 2D: simple stack order (higher index = rendered on top)
      zip (lsLayers stack) [1..]
  
  | all is3DLayer (lsLayers stack) =
      -- All 3D: sort by Z depth (smaller Z = further from camera = rendered first)
      sortBy (comparing layerZPosition) (lsLayers stack) `zip` [1..]
  
  | otherwise =
      -- Mixed: 2D groups interrupt 3D sorting
      interleave3D2D (lsLayers stack)

-- | CRITICAL KNOWLEDGE: 2D layers between 3D layers create "render breaks"
-- | This is how you control whether particles go in front or behind something
renderBreakRules :: [Text]
renderBreakRules =
  [ "3D layers sort among themselves by Z depth"
  , "A 2D layer in the stack creates a 'render break'"
  , "3D layers above the 2D layer form a NEW sort group"
  , "Use 2D layers strategically to control occlusion"
  , "Example: Person on Layer 3 (3D), Background on Layer 5 (3D)"
  , "  Particles on Layer 2 (3D) would sort with Layers 3 and 5"
  , "  Put a 2D Null on Layer 4: Now particles sort with Layer 3 only"
  , "  This makes particles appear IN FRONT of background regardless of Z"
  ]
```

### 2.3 Parent-Child Relationships

```yaml
parenting:
  description: >
    Any layer can be parented to another layer. The child inherits
    the parent's transform but maintains its own relative transform.
    THIS IS HOW COMPLEX MOTION IS BUILT.

  parent_child_mechanics:
    what_inherits:
      - "Position"
      - "Scale"
      - "Rotation"
      - "Anchor point movement"
    what_doesnt_inherit:
      - "Opacity"
      - "Effects"
      - "Blending mode"
      
  common_patterns:
    orbit:
      description: "Child orbits parent by rotating parent"
      setup:
        - "Create null at orbit center"
        - "Parent orbiting object to null"
        - "Position child offset from null center"
        - "Animate null rotation"
      why_works: "Child position is relative to parent; rotation carries it around"
      
    follow:
      description: "Multiple objects follow leader"
      setup:
        - "Create leader layer (or null)"
        - "Parent followers to leader"
        - "Add position offset to each follower"
        - "Animate only the leader"
      benefit: "Animate once, all follow"
      
    complex_rig:
      description: "Hierarchical character/machine rig"
      example: "Arm rig"
      setup:
        - "Upper arm parented to body"
        - "Lower arm parented to upper arm"
        - "Hand parented to lower arm"
        - "Rotating upper arm moves entire arm chain"
      principle: "Parent = pivot point for all children"

  null_layer_mastery:
    philosophy: >
      NULL LAYERS ARE THE MOST POWERFUL TOOL IN MOTION GRAPHICS.
      They are invisible control points. Whenever you need to:
      - Control multiple layers as one
      - Create a pivot point that isn't at layer center
      - Drive expressions from a single source
      - Create orbital motion
      USE A NULL LAYER.
    
    examples:
      group_entrance:
        problem: "5 elements should slide in together"
        amateur: "Keyframe all 5 positions separately"
        professional: "Parent all 5 to null, animate null position"
        benefit: "One set of keyframes, easy timing adjustment"
        
      rotation_pivot:
        problem: "Rotate logo around corner, not center"
        amateur: "Try to offset position while rotating (painful)"
        professional: "Create null at corner, parent logo, rotate null"
        
      camera_control:
        problem: "Camera should orbit around product"
        setup: "Parent camera to null at product center, rotate null"
```

---

## 3. Z-Space & 3D Composition

### 3.1 Understanding 3D Space

```haskell
-- | The compositor's understanding of 3D space
data Space3D = Space3D
  { s3dCoordinateSystem :: !CoordinateSystem
  , s3dCameraSetup :: !CameraConfig
  , s3dLayerDepths :: ![(LayerId, ZPosition)]
  } deriving (Eq, Show, Generic)

data CoordinateSystem = CoordinateSystem
  { csXAxis :: !AxisDefinition  -- Right is positive
  , csYAxis :: !AxisDefinition  -- DOWN is positive (screen coords)
  , csZAxis :: !AxisDefinition  -- TOWARD camera is positive (negative = further)
  } deriving (Eq, Show, Generic)

-- | After Effects 3D coordinate system
aeCoordinateSystem :: CoordinateSystem
aeCoordinateSystem = CoordinateSystem
  { csXAxis = AxisDefinition "Right" Positive
  , csYAxis = AxisDefinition "Down" Positive   -- NOTE: Not standard 3D!
  , csZAxis = AxisDefinition "Toward camera" Positive
  }

-- | Lottie/Web coordinate system (what we output)
webCoordinateSystem :: CoordinateSystem
webCoordinateSystem = CoordinateSystem
  { csXAxis = AxisDefinition "Right" Positive
  , csYAxis = AxisDefinition "Down" Positive
  , csZAxis = AxisDefinition "Toward viewer" Positive  -- CSS transform-style: preserve-3d
  }
```

### 3.2 Spatial Relationships

```yaml
spatial_planning:
  description: >
    When a user says "particles circle around the person," the AI must
    plan the spatial relationships in 3D.

  analysis_steps:
    1_identify_layers:
      input: "User's description + layer stack"
      output: "Which layer is the person? Which is background?"
      method:
        - "Parse layer names for semantic content"
        - "Use image analysis on layer contents"
        - "Infer from context (e.g., layer 3 often middle = subject)"
    
    2_establish_z_positions:
      background: "Z = -1000 (far from camera)"
      subject: "Z = 0 (default depth)"
      particles: "Z varies from -500 to +500 (orbiting)"
      foreground: "Z = +500 (close to camera)"
      
    3_plan_motion_path:
      circle_around:
        technique: "3D circular path in XZ plane (horizontal circle)"
        implementation:
          - "Create null at subject center"
          - "Position particles offset in X or Z"
          - "Parent particles to null"
          - "Animate null Y rotation for horizontal orbit"
          - "OR: Use expression for circular motion"
        expression: |
          radius = 200;
          speed = 1; // revolutions per second
          angle = time * speed * 360;
          x = Math.cos(degreesToRadians(angle)) * radius;
          z = Math.sin(degreesToRadians(angle)) * radius;
          [value[0] + x, value[1], value[2] + z]
          
    4_handle_occlusion:
      problem: "Particles should pass in front AND behind person"
      solution_a: "True 3D with depth sorting"
      solution_b: "Duplicate person layer, sandwich particles"
      solution_c: "Matte/mask particles when behind"
      
      true_3d_approach:
        - "Enable 3D on all relevant layers"
        - "Position person at Z = 0"
        - "Particles orbit at various Z values"
        - "3D depth sorting handles occlusion automatically"
        - "Background must be at Z < particle minimum"
        
      sandwich_approach:
        - "Duplicate person layer"
        - "Original person at Z = 0"
        - "Particles at Z = varies"
        - "Person duplicate at Z = person - 1"
        - "Use track matte to reveal only the 'behind' area"

  spiral_motion:
    description: "Particles spiral around person 3 times then exit"
    components:
      - "Circular motion in XZ plane (orbiting)"
      - "Ascending motion in Y (spiral upward)"
      - "Radial motion (spiral in or out)"
      - "Linear exit motion after spirals complete"
      
    implementation:
      expression_based: |
        // Spiral 3 times over 3 seconds, then exit
        spiralDuration = 3;
        spiralRevolutions = 3;
        exitDuration = 1;
        
        if (time < spiralDuration) {
          // Spiral phase
          progress = time / spiralDuration;
          angle = progress * spiralRevolutions * 360;
          radius = 150 - (progress * 50); // Spiral inward
          yOffset = progress * 200; // Rise while spiraling
          
          x = Math.cos(degreesToRadians(angle)) * radius;
          z = Math.sin(degreesToRadians(angle)) * radius;
          y = yOffset;
          
          [anchorX + x, anchorY - y, z]
        } else {
          // Exit phase - fly off to the left
          exitProgress = (time - spiralDuration) / exitDuration;
          exitProgress = Math.min(exitProgress, 1);
          
          // Ease out the exit
          exitEased = 1 - Math.pow(1 - exitProgress, 3);
          
          // Final spiral position
          finalX = anchorX + Math.cos(degreesToRadians(3 * 360)) * 100;
          finalY = anchorY - 200;
          finalZ = Math.sin(degreesToRadians(3 * 360)) * 100;
          
          // Exit to the left
          exitX = finalX - (1920 * exitEased);
          
          [exitX, finalY, finalZ]
        }
```

### 3.3 Camera Knowledge

```haskell
-- | Camera configuration and behavior
data CameraConfig = CameraConfig
  { ccType :: !CameraType
  , ccZoom :: !Pixels           -- Focal length equivalent
  , ccPosition :: !Point3D
  , ccPointOfInterest :: !Point3D
  , ccDepthOfField :: !(Maybe DOFConfig)
  } deriving (Eq, Show, Generic)

data CameraType
  = CTOneNode    -- Position only, always looks at comp center
  | CTTwoNode    -- Position + Point of Interest (look target)
  deriving (Eq, Show, Enum, Bounded)

-- | Standard camera setups
standardCameras :: Map Text CameraConfig
standardCameras = Map.fromList
  [ ("default_50mm", CameraConfig
      { ccType = CTTwoNode
      , ccZoom = 1777.78  -- 50mm equivalent
      , ccPosition = Point3D 960 540 (-2000)
      , ccPointOfInterest = Point3D 960 540 0
      , ccDepthOfField = Nothing
      })
  
  , ("wide_24mm", CameraConfig
      { ccType = CTTwoNode
      , ccZoom = 852.07   -- 24mm equivalent (wider view)
      , ccPosition = Point3D 960 540 (-1500)
      , ccPointOfInterest = Point3D 960 540 0
      , ccDepthOfField = Nothing
      })
      
  , ("telephoto_85mm", CameraConfig
      { ccType = CTTwoNode
      , ccZoom = 3019.56  -- 85mm equivalent (flatter, portrait)
      , ccPosition = Point3D 960 540 (-3000)
      , ccPointOfInterest = Point3D 960 540 0
      , ccDepthOfField = Nothing
      })
  ]

-- | Camera motion patterns
data CameraMotion
  = CMPush           -- Move toward subject (zoom effect)
  | CMPull           -- Move away from subject
  | CMPan            -- Horizontal rotation around interest point
  | CMTilt           -- Vertical rotation
  | CMTruck          -- Horizontal slide (left/right)
  | CMPedestal       -- Vertical slide (up/down)
  | CMOrbit          -- Full rotation around subject
  | CMDollyZoom      -- "Vertigo" effect: zoom while moving (keeps subject size)
  deriving (Eq, Show, Enum, Bounded)

-- | Camera technique documentation
cameraKnowledge :: [(CameraMotion, Text)]
cameraKnowledge =
  [ (CMPush, "Push into scene creates intimacy, focus, revelation")
  , (CMPull, "Pull out reveals context, creates distance, ending")
  , (CMPan, "Pan follows action or reveals environment")
  , (CMTilt, "Tilt emphasizes height or looks up/down")
  , (CMOrbit, "Orbit around product = premium, showcase")
  , (CMDollyZoom, "Subject stays same size, background warps = unease")
  ]
```

---

## 4. Keyframe Mechanics

### 4.1 Keyframe Deep Understanding

```yaml
keyframe_fundamentals:
  definition: >
    A keyframe records a property value at a specific time.
    The compositor interpolates values between keyframes.
    KEYFRAMES ARE THE ATOMS OF ANIMATION.

  keyframe_types:
    linear:
      symbol: "Diamond (◇)"
      interpolation: "Constant rate between keyframes"
      use_case: "Mechanical motion, specific rate needed"
      feel: "Robotic"
      
    bezier:
      symbol: "Hourglass (⏳)"  
      interpolation: "Curved rate controlled by handles"
      use_case: "Natural motion, ease-in, ease-out"
      subtypes:
        ease_in: "Starts slow, ends fast"
        ease_out: "Starts fast, ends slow"
        ease_both: "S-curve, natural feel"
      feel: "Organic"
      
    hold:
      symbol: "Square (◼)"
      interpolation: "No interpolation - instant jump"
      use_case: "Visibility toggles, state changes"
      feel: "Instant, digital"
      
    auto_bezier:
      symbol: "Circle (●)"
      interpolation: "Automatically smooth through point"
      use_case: "Smooth path through multiple points"
      
  spatial_vs_temporal:
    critical_concept: >
      Position keyframes have TWO types of interpolation:
      1. SPATIAL - The PATH the object takes through space
      2. TEMPORAL - The SPEED at which it travels that path
      
    spatial_interpolation:
      linear: "Straight line between positions (corners)"
      bezier: "Curved path (smooth arc)"
      control: "Drag the position keyframe's spatial handles"
      
    temporal_interpolation:
      linear: "Constant speed along path"
      bezier: "Accelerating/decelerating along path"
      control: "Graph editor or keyframe velocity"
      
    common_mistake: >
      Novices set easing on keyframes and expect smooth PATHS.
      But easing affects TIMING, not PATH.
      To get curved PATHS, you must adjust SPATIAL bezier handles
      or convert position keyframes to bezier spatial interpolation.

  graph_editor:
    purpose: "Precise control of animation timing"
    views:
      value_graph: "Y-axis = property value, X-axis = time"
      speed_graph: "Y-axis = velocity, X-axis = time"
      
    reading_value_graph:
      steep_curve: "Fast change (high speed)"
      flat_curve: "No change (stopped)"
      s_curve: "Ease in then ease out"
      
    manipulation:
      bezier_handles: "Drag to shape the curve"
      split_handles: "Alt+drag for asymmetric easing"
      easy_ease: "Automatic smooth curve (often too much)"
      
    best_practices:
      - "Never use Easy Ease blindly - check the graph"
      - "Steeper ease-out than ease-in for natural arrival"
      - "Zero velocity at hold positions"
      - "Match velocities at transitions for smooth movement"
```

### 4.2 Keyframe Patterns

```haskell
-- | Common keyframe patterns a master compositor knows
data KeyframePattern = KeyframePattern
  { kpName :: !Text
  , kpDescription :: !Text
  , kpKeyframes :: ![RelativeKeyframe]
  , kpWhenToUse :: ![UseCase]
  } deriving (Eq, Show, Generic)

data RelativeKeyframe = RelativeKeyframe
  { rkTimePercent :: !Float      -- 0.0 to 1.0 of total duration
  , rkValuePercent :: !Float     -- 0.0 to 1.0 of value change
  , rkInterpolation :: !Interpolation
  , rkVelocity :: !(Maybe Float) -- Optional velocity at keyframe
  } deriving (Eq, Show, Generic)

-- | Master keyframe patterns
masterPatterns :: [KeyframePattern]
masterPatterns =
  [ KeyframePattern
      "Basic Ease Out"
      "Start fast, end slow. Most common arrival pattern."
      [ RelativeKeyframe 0.0 0.0 EaseOut Nothing
      , RelativeKeyframe 1.0 1.0 Linear (Just 0)  -- Zero velocity at end
      ]
      [UCEntrance, UCArrival]
  
  , KeyframePattern
      "Overshoot and Settle"
      "Go past target, then settle back. Organic, playful."
      [ RelativeKeyframe 0.0 0.0 EaseOut Nothing
      , RelativeKeyframe 0.7 1.15 EaseInOut Nothing  -- 15% overshoot
      , RelativeKeyframe 1.0 1.0 EaseIn (Just 0)
      ]
      [UCEntrance, UCEmphasis, UCPlayful]
      
  , KeyframePattern
      "Anticipation and Action"
      "Wind up before main action. Disney principle."
      [ RelativeKeyframe 0.0 0.0 EaseOut Nothing
      , RelativeKeyframe 0.2 (-0.1) EaseInOut Nothing  -- Wind up (opposite direction)
      , RelativeKeyframe 1.0 1.0 EaseOut (Just 0)
      ]
      [UCDramatic, UCCharacter, UCEmphasis]
      
  , KeyframePattern
      "Pop"
      "Quick scale up, brief hold, subtle settle."
      [ RelativeKeyframe 0.0 0.0 EaseOut Nothing
      , RelativeKeyframe 0.3 1.1 EaseOut Nothing   -- Fast to overshoot
      , RelativeKeyframe 0.45 1.1 Hold Nothing     -- Brief hold at peak
      , RelativeKeyframe 1.0 1.0 EaseInOut (Just 0)  -- Settle
      ]
      [UCEmphasis, UCNotification, UCSuccess]
      
  , KeyframePattern
      "Bounce"
      "Physics bounce with decreasing amplitude."
      [ RelativeKeyframe 0.0 0.0 EaseIn Nothing    -- Accelerating fall
      , RelativeKeyframe 0.3 1.0 Linear Nothing    -- Impact
      , RelativeKeyframe 0.45 0.85 EaseOut Nothing -- First bounce
      , RelativeKeyframe 0.55 1.0 EaseIn Nothing   -- Fall
      , RelativeKeyframe 0.7 0.95 EaseOut Nothing  -- Second bounce
      , RelativeKeyframe 0.8 1.0 EaseIn Nothing    -- Fall
      , RelativeKeyframe 1.0 1.0 EaseOut (Just 0)  -- Settle
      ]
      [UCPlayful, UCPhysics, UCCartoon]
      
  , KeyframePattern
      "Cinematic Reveal"
      "Slow build, moment of arrival, subtle settle."
      [ RelativeKeyframe 0.0 0.0 EaseIn Nothing    -- Slow start
      , RelativeKeyframe 0.8 0.95 EaseOut Nothing  -- Building
      , RelativeKeyframe 0.9 1.0 EaseOut Nothing   -- Arrival moment
      , RelativeKeyframe 1.0 1.0 Hold (Just 0)     -- Hold at reveal
      ]
      [UCReveal, UCLuxury, UCDramatic]
  ]

-- | Generate keyframes from pattern
generateKeyframes :: KeyframePattern -> Duration -> PropertyValue -> PropertyValue -> [Keyframe]
generateKeyframes pattern duration startVal endVal =
  let valueRange = endVal - startVal
      durationMs = durationToMs duration
  in map (toKeyframe durationMs startVal valueRange) (kpKeyframes pattern)
  where
    toKeyframe durMs start range rk = Keyframe
      { kfTime = durMs * rkTimePercent rk
      , kfValue = start + (range * rkValuePercent rk)
      , kfInterpolation = rkInterpolation rk
      , kfVelocity = rkVelocity rk
      }
```

### 4.3 Multi-Property Coordination

```yaml
property_coordination:
  principle: >
    Great animation coordinates multiple properties with intention.
    Each property's timing is slightly offset to create "follow-through"
    and avoid mechanical uniformity.

  coordination_patterns:
    scale_before_position:
      description: "Object scales up slightly before moving"
      timing: "Scale starts 2-4 frames before position"
      why: "Creates sense of energy gathering before motion"
      
    opacity_with_scale:
      description: "Fade and scale together for entries"
      timing: "Start simultaneously, opacity finishes slightly before scale"
      why: "Object solidifies before fully arriving"
      
    position_leads_rotation:
      description: "Object moves, rotation follows"
      timing: "Rotation starts 2-3 frames after position"
      why: "Creates drag, weight, follow-through"
      
    staggered_properties:
      description: "Each property peaks at different time"
      example:
        frame_0: "Position starts"
        frame_3: "Scale starts"
        frame_6: "Rotation starts"
        frame_15: "Position peaks"
        frame_17: "Scale peaks"
        frame_20: "Rotation peaks"
      why: "Creates organic, non-mechanical motion"

  the_one_frame_rule:
    description: >
      Offsetting properties by even ONE FRAME creates significantly
      more natural motion. The human eye detects perfect synchronization
      as artificial.
    
    application:
      - "Secondary properties: +1-2 frames"
      - "Tertiary properties: +2-4 frames"
      - "Never let all properties share keyframes exactly"
```

---

## 5. Expressions & Automation

### 5.1 Expression Fundamentals

```yaml
expressions_knowledge:
  definition: >
    Expressions are code snippets that DRIVE property values dynamically.
    Instead of keyframes defining exact values at exact times,
    expressions CALCULATE values based on time, other properties, or external data.

  when_to_use:
    perfect_for:
      - "Continuous/looping motion (wiggle, wave, orbit)"
      - "Linking properties (scale X = scale Y)"
      - "Complex math-driven motion"
      - "Responsive/dynamic behavior"
      - "Audio-reactive animation"
      
    not_ideal_for:
      - "Simple A-to-B motion (keyframes are clearer)"
      - "Highly specific timing (hard to tweak)"
      - "Hand-crafted character animation"

  essential_expressions:
    wiggle:
      syntax: "wiggle(frequency, amplitude)"
      example: "wiggle(2, 20)  // 2 oscillations per second, 20 pixel amplitude"
      use: "Organic randomness, handheld camera, subtle life"
      
    loop_out:
      syntax: "loopOut(type, numKeyframes)"
      types: ["cycle", "pingpong", "offset", "continue"]
      example: "loopOut('pingpong')  // Rock back and forth forever"
      use: "Repeating animation without duplicating keyframes"
      
    time:
      description: "Current composition time in seconds"
      example: "Math.sin(time * 2 * Math.PI) * 50  // Sine wave at 1Hz"
      use: "Any time-based calculation"
      
    value:
      description: "Current property value (or keyframed value)"
      example: "value + [100, 0]  // Offset from keyframed position"
      use: "Modify existing keyframed animation"
      
    valueAtTime:
      syntax: "valueAtTime(time)"
      example: "thisComp.layer('control').transform.position.valueAtTime(time - 0.1)"
      use: "Delayed following, time offsets"
      
    linear:
      syntax: "linear(value, inputMin, inputMax, outputMin, outputMax)"
      example: "linear(time, 0, 3, 0, 100)  // 0→100 over 3 seconds"
      use: "Remapping values"
      
    ease:
      syntax: "ease(value, inputMin, inputMax, outputMin, outputMax)"
      example: "ease(time, 0, 3, 0, 100)  // Eased 0→100 over 3 seconds"
      use: "Smooth value remapping"
```

### 5.2 Advanced Expression Patterns

```haskell
-- | Expression patterns that expert compositors use
data ExpressionPattern = ExpressionPattern
  { epName :: !Text
  , epDescription :: !Text
  , epCode :: !Text
  , epUseCase :: !Text
  } deriving (Eq, Show, Generic)

advancedExpressions :: [ExpressionPattern]
advancedExpressions =
  [ ExpressionPattern
      "Circular Motion"
      "Object moves in a perfect circle"
      [r|
        radius = 150;
        speed = 1; // revolutions per second
        angle = time * speed * Math.PI * 2;
        center = [960, 540];
        x = center[0] + Math.cos(angle) * radius;
        y = center[1] + Math.sin(angle) * radius;
        [x, y]
      |]
      "Orbiting elements, loading animations"
  
  , ExpressionPattern
      "Spiral Motion"
      "Object spirals outward or inward"
      [r|
        startRadius = 50;
        endRadius = 200;
        revolutions = 3;
        duration = 2; // seconds
        
        progress = Math.min(time / duration, 1);
        angle = progress * revolutions * Math.PI * 2;
        radius = startRadius + (endRadius - startRadius) * progress;
        
        center = [960, 540];
        x = center[0] + Math.cos(angle) * radius;
        y = center[1] + Math.sin(angle) * radius;
        [x, y]
      |]
      "Particle dispersal, energy effects"
  
  , ExpressionPattern
      "Follow with Delay"
      "Object follows another with time offset"
      [r|
        leader = thisComp.layer("Leader");
        delay = 0.1; // seconds
        leader.transform.position.valueAtTime(time - delay)
      |]
      "Snake motion, trailing elements"
  
  , ExpressionPattern
      "Inertial Bounce"
      "Physics-based bounce on value change"
      [r|
        // Attempt to find most recent keyframe
        n = 0;
        if (numKeys > 0) {
          n = nearestKey(time).index;
          if (key(n).time > time) n--;
        }
        if (n == 0) {
          value;
        } else {
          freq = 3;       // oscillation frequency
          decay = 5;      // decay speed
          t = time - key(n).time;
          startVal = key(n).value;
          vel = velocityAtTime(key(n).time - 0.001);
          amp = vel / freq;
          startVal + amp * Math.sin(freq * t * Math.PI * 2) / Math.exp(decay * t);
        }
      |]
      "Springy overshoot, organic settle"
  
  , ExpressionPattern
      "Random but Consistent"
      "Random value that stays consistent (seedRandom)"
      [r|
        seedRandom(index, true);
        random(0, 100)  // Each layer gets different random, but consistent per layer
      |]
      "Varied elements with consistent result"
  
  , ExpressionPattern
      "Look At / Auto Orient"
      "Rotate to face another point"
      [r|
        target = thisComp.layer("Target").transform.position;
        delta = target - transform.position;
        radiansToDegrees(Math.atan2(delta[1], delta[0]))
      |]
      "Arrows pointing at cursor, eyes following"
  
  , ExpressionPattern
      "Progress-Based Reveal"
      "Property changes based on external progress"
      [r|
        control = thisComp.layer("Control").effect("Slider Control")("Slider");
        linear(control, 0, 100, transform.opacity)
      |]
      "Keyframe-less control via sliders"
  ]
```

---

## 6. Nested Compositions

### 6.1 Pre-Composition Mastery

```yaml
precomp_philosophy:
  definition: >
    A pre-composition (precomp) is a composition used as a layer
    in another composition. It's the MODULAR UNIT of motion graphics.

  when_to_precomp:
    complexity_management:
      - "More than 20 layers → precomp related groups"
      - "Repeated elements → precomp and duplicate"
      - "Complex effect chain → isolate in precomp"
      
    render_control:
      - "Need to affect group as one (blur, color)"
      - "Need collapsed transforms for 3D"
      - "Need motion blur on group"
      
    reusability:
      - "Same animation used multiple times"
      - "Building a template library"
      - "Creating 'master' elements"

  precomp_techniques:
    collapse_transformations:
      description: "Render precomp layers in parent space, not flat"
      when_on: "3D layers in precomp should sort with parent 3D layers"
      when_off: "Precomp should render flat, then transform as 2D"
      critical: "MOST COMMON PRECOMP CONFUSION"
      
    time_remapping:
      description: "Control precomp's internal time with keyframes"
      use_cases:
        - "Slow motion sections"
        - "Freeze frames"
        - "Reverse playback"
        - "Looping specific segments"
      expression: "loopOut('cycle')  // Infinite loop of precomp"
      
    size_inheritance:
      description: "Precomp has its own size"
      gotcha: "Content outside precomp bounds is clipped"
      fix: "Make precomp larger than needed, or enable 'Continuously Rasterize'"

  precomp_architecture:
    small_project: |
      Main Comp
      ├── Background (solid/image)
      ├── Content Group (precomp)
      │   ├── Element A
      │   ├── Element B
      │   └── Element C
      └── Overlays (precomp)
          ├── Logo
          └── CTA
          
    medium_project: |
      Master Comp
      ├── Intro Scene (precomp)
      │   ├── Intro Background
      │   └── Intro Content
      ├── Main Scene (precomp)
      │   ├── Main Background
      │   └── Main Content (precomp)
      │       ├── Product
      │       ├── Features
      │       └── CTA
      └── Outro Scene (precomp)
      
    complex_project: |
      Final Output
      ├── Scene Container (precomp, time-remapped)
      │   ├── Scene 1 (precomp)
      │   ├── Transition 1-2 (precomp)
      │   ├── Scene 2 (precomp)
      │   ├── Transition 2-3 (precomp)
      │   └── Scene 3 (precomp)
      ├── Global Overlays (precomp)
      ├── Audio (precomp)
      └── Adjustment Layers
```

### 6.2 Composition Planning for the AI

```haskell
-- | The AI must plan composition structure before building
data CompositionPlan = CompositionPlan
  { cpMainComp :: !CompDefinition
  , cpPrecomps :: ![CompDefinition]
  , cpLayerAssignments :: ![(Element, CompId, LayerIndex)]
  , cpParentingPlan :: ![(LayerId, LayerId)]
  , cp3DPlan :: ![(LayerId, Bool)]  -- Which layers are 3D
  } deriving (Eq, Show, Generic)

data CompDefinition = CompDefinition
  { cdId :: !CompId
  , cdName :: !Text
  , cdSize :: !(Int, Int)
  , cdDuration :: !Duration
  , cdFrameRate :: !Float
  , cdPurpose :: !CompPurpose
  } deriving (Eq, Show, Generic)

data CompPurpose
  = CPMain           -- Final output
  | CPScene          -- Scene container
  | CPElementGroup   -- Grouped elements
  | CPReusable       -- Template element
  | CPControl        -- Control layers (nulls, etc.)
  deriving (Eq, Show, Enum, Bounded)

-- | Plan composition structure for user request
planComposition :: UserRequest -> ImageAnalysis -> CompositionPlan
planComposition request analysis =
  let -- Identify all elements that need animation
      elements = identifyElements analysis
      
      -- Group related elements
      groups = groupRelatedElements elements
      
      -- Determine 3D needs
      needs3D = analyzeSpacialNeeds request
      
      -- Create precomp for each logical group
      precomps = map createPrecompDef groups
      
      -- Plan layer assignments
      assignments = planLayerAssignments elements precomps
      
      -- Plan parenting hierarchy
      parenting = planParentingHierarchy request elements
      
  in CompositionPlan
       { cpMainComp = createMainComp analysis
       , cpPrecomps = precomps
       , cpLayerAssignments = assignments
       , cpParentingPlan = parenting
       , cp3DPlan = plan3DLayers needs3D elements
       }

-- | Example: "particles circle the person"
-- | AI plans:
-- |   Main Comp (1920x1080, 4s)
-- |   ├── Background Layer (2D, bottom)
-- |   ├── Particles Precomp (3D enabled)
-- |   │   └── [20 particle layers, all 3D]
-- |   ├── Person Layer (3D, Z=0)
-- |   └── Control Null (parent for particle orbit)
```

---

## 7. Execution Translation

### 7.1 From Intent to Layer Instructions

```yaml
intent_to_execution:
  description: >
    When user says something like "particles circle the person in 3D,
    spiral 3 times, then exit left," the AI must translate this into
    EXACT compositor instructions.

  example_translation:
    user_request: >
      "Make the particles slower, fade from red to green over 3 seconds,
      circle the person 3 times, then fly off to the left"
    
    parsed_intent:
      target: "particles"
      actions:
        - type: "speed_change"
          direction: "slower"
          amount: "unspecified - use 30% reduction"
        - type: "color_change"
          from: "red"
          to: "green"
          duration: "3 seconds"
        - type: "spatial_motion"
          pattern: "circle"
          around: "person"
          repetitions: 3
        - type: "exit_motion"
          direction: "left"
          timing: "after circle completes"
    
    layer_identification:
      method: "Semantic analysis of layer names + image content"
      person_layer: "Layer 3 (name contains 'person' OR image analysis detects human)"
      particle_layers: "Layers 6-25 (name contains 'particle' OR visual analysis)"
      background_layer: "Layer 5 (largest layer OR name contains 'background')"
    
    compositor_instructions:
      step_1_adjust_speed:
        action: "Scale time"
        method: "Multiply all particle animation durations by 1.3"
        keyframes: "Stretch existing keyframes proportionally"
        
      step_2_color_animation:
        property: "Fill Color on each particle layer"
        keyframe_1:
          time: "0s"
          value: "#FF0000 (red)"
          interpolation: "linear"
        keyframe_2:
          time: "3s"
          value: "#00FF00 (green)"
          interpolation: "linear"
          
      step_3_3d_setup:
        enable_3d:
          - "Person layer"
          - "All particle layers"
          - "Background layer"
        z_positions:
          background: -500
          person: 0
          particles: "will vary during orbit"
          
      step_4_orbit_setup:
        create_null: "Orbit_Control at person center"
        parent_particles: "All particles to Orbit_Control"
        distribute_particles: "Spread around null in circle, various Z offsets"
        
      step_5_orbit_animation:
        property: "Orbit_Control Y Rotation"
        expression_or_keyframes: "keyframes for control"
        keyframe_1:
          time: "0s"
          value: "0°"
        keyframe_2:
          time: "3s"  
          value: "1080°"  # 3 full rotations
          interpolation: "ease_in_out"
          
      step_6_exit_animation:
        timing: "starts at 3s (after orbit)"
        property: "Orbit_Control Position X"
        keyframe_1:
          time: "3s"
          value: "current_position"
        keyframe_2:
          time: "4s"
          value: "-500"  # Off screen left
          interpolation: "ease_in"
```

### 7.2 Layer-by-Layer Build Instructions

```haskell
-- | The AI generates step-by-step build instructions
data BuildInstruction
  = BICreateLayer !LayerSpec
  | BISetProperty !LayerId !PropertyPath !PropertyValue
  | BIAddKeyframe !LayerId !PropertyPath !Keyframe
  | BISetExpression !LayerId !PropertyPath !Text
  | BIParentTo !LayerId !LayerId
  | BIEnable3D !LayerId
  | BISetBlendMode !LayerId !BlendMode
  | BIAddEffect !LayerId !EffectSpec
  | BIPrecompose ![LayerId] !Text
  | BIComment !Text  -- Documentation for the build
  deriving (Eq, Show, Generic)

-- | Generate build instructions for particle orbit example
generateOrbitInstructions :: Request -> Analysis -> [BuildInstruction]
generateOrbitInstructions request analysis =
  [ BIComment "=== PARTICLE ORBIT BUILD ==="
  
  -- Step 1: Identify and prepare existing layers
  , BIComment "--- Layer Preparation ---"
  , BIEnable3D (LayerId "person")
  , BISetProperty (LayerId "person") ["transform", "position", "z"] (NumberVal 0)
  , BIEnable3D (LayerId "background")
  , BISetProperty (LayerId "background") ["transform", "position", "z"] (NumberVal (-500))
  
  -- Step 2: Create control null
  , BIComment "--- Control Null Setup ---"
  , BICreateLayer $ LayerSpec
      { lsType = NullObject
      , lsName = "Orbit_Control"
      , lsPosition = personCenter analysis
      , ls3D = True
      }
  
  -- Step 3: Setup each particle
  , BIComment "--- Particle Setup ---"
  ] ++ concatMap setupParticle (particleLayers analysis)
  ++ [
  -- Step 4: Orbit animation
    BIComment "--- Orbit Animation ---"
  , BIAddKeyframe (LayerId "Orbit_Control") 
      ["transform", "yRotation"] 
      (Keyframe 0 0 EaseInOut Nothing)
  , BIAddKeyframe (LayerId "Orbit_Control") 
      ["transform", "yRotation"] 
      (Keyframe 3000 1080 EaseInOut Nothing)
  
  -- Step 5: Exit animation
  , BIComment "--- Exit Animation ---"
  , BIAddKeyframe (LayerId "Orbit_Control")
      ["transform", "position", "x"]
      (Keyframe 3000 (centerX analysis) EaseIn Nothing)
  , BIAddKeyframe (LayerId "Orbit_Control")
      ["transform", "position", "x"]
      (Keyframe 4000 (-500) EaseIn Nothing)
  
  -- Step 6: Color animation on particles
  , BIComment "--- Color Animation ---"
  ] ++ map addColorAnimation (particleLayers analysis)
  where
    setupParticle pid = 
      [ BIEnable3D pid
      , BIParentTo pid (LayerId "Orbit_Control")
      , BISetProperty pid ["transform", "position", "z"] (NumberVal (randomZ pid))
      ]
    
    addColorAnimation pid =
      [ BIAddKeyframe pid ["content", "fill", "color"]
          (Keyframe 0 (ColorVal "#FF0000") Linear Nothing)
      , BIAddKeyframe pid ["content", "fill", "color"]
          (Keyframe 3000 (ColorVal "#00FF00") Linear Nothing)
      ]
    
    randomZ pid = (hash pid `mod` 300) - 150  -- -150 to +150 Z spread
```

---

## 8. Constraint Summary

| Concept | AI Must Know |
|---------|-------------|
| Layer Order | Higher index = renders on top (2D); Z-depth sorts 3D |
| Anchor Point | MUST set correctly for natural rotation/scale |
| Parenting | Child inherits parent transform; null layers are control points |
| 3D Space | Y is DOWN; 2D layers create render breaks in 3D sort |
| Keyframes | Spatial vs temporal interpolation are DIFFERENT |
| Expressions | Use for dynamic/looping; keyframes for specific timing |
| Precomps | Modular units; collapse transforms for 3D continuity |

| User Request Pattern | Compositor Response |
|---------------------|---------------------|
| "Circle around X" | Parent to null at X center, rotate null |
| "Fly off screen" | Position keyframes to -100 or +canvas+100 |
| "In front of / behind" | Z-position in 3D OR layer order in 2D |
| "Follow each other" | Parent chain OR expression with time delay |
| "Spiral" | Rotation + radial position change + optional Y |
| "Fade from A to B" | Color keyframes with linear interpolation |

---

*End of Specification 28*
