<template>
  <div class="particle-properties">
    <!-- Presets Section -->
    <div class="property-section presets-section">
      <div class="section-header" @click="toggleSection('presets')">
        <i class="pi" :class="expandedSections.has('presets') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Presets</span>
      </div>
      <div v-if="expandedSections.has('presets')" class="section-content">
        <div class="preset-controls">
          <select v-model="selectedPresetId" class="preset-select">
            <option value="">Select a preset...</option>
            <optgroup label="Built-in">
              <option v-for="p in builtInPresets" :key="p.id" :value="p.id">
                {{ p.name }}
              </option>
            </optgroup>
            <optgroup v-if="userPresets.length > 0" label="User Presets">
              <option v-for="p in userPresets" :key="p.id" :value="p.id">
                {{ p.name }}
              </option>
            </optgroup>
          </select>
          <button class="preset-btn apply" @click="applySelectedPreset" :disabled="!selectedPresetId" title="Apply Preset">
            Apply
          </button>
        </div>
        <div class="preset-actions">
          <button class="preset-btn save" @click="showSaveDialog = true" title="Save Current Settings as Preset">
            Save Preset
          </button>
          <button class="preset-btn delete" @click="deleteSelectedPreset" :disabled="!selectedPresetId || isBuiltInPreset" title="Delete Preset">
            Delete
          </button>
        </div>
      </div>
    </div>

    <!-- Save Preset Dialog -->
    <div v-if="showSaveDialog" class="preset-dialog-overlay" @click.self="showSaveDialog = false">
      <div class="preset-dialog">
        <h3>Save Particle Preset</h3>
        <div class="dialog-field">
          <label>Name</label>
          <input v-model="newPresetName" type="text" placeholder="My Preset" />
        </div>
        <div class="dialog-field">
          <label>Description</label>
          <input v-model="newPresetDescription" type="text" placeholder="Optional description..." />
        </div>
        <div class="dialog-field">
          <label>Tags (comma-separated)</label>
          <input v-model="newPresetTags" type="text" placeholder="fire, glow, magic" />
        </div>
        <div class="dialog-actions">
          <button class="dialog-btn cancel" @click="showSaveDialog = false">Cancel</button>
          <button class="dialog-btn save" @click="saveCurrentAsPreset" :disabled="!newPresetName.trim()">Save</button>
        </div>
      </div>
    </div>

    <!-- System Settings -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('system')">
        <i class="pi" :class="expandedSections.has('system') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>System Settings</span>
      </div>
      <div v-if="expandedSections.has('system')" class="section-content">
        <div class="property-row">
          <label title="Maximum number of particles that can exist at once. Higher values create denser effects but use more memory.">Max Particles</label>
          <input
            type="range"
            :value="systemConfig.maxParticles"
            min="100"
            max="50000"
            step="100"
            @input="updateSystemConfig('maxParticles', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ systemConfig.maxParticles }}</span>
        </div>
        <div class="property-row">
          <label title="Global gravity force. Positive values pull particles down, negative values push them up.">Gravity</label>
          <input
            type="range"
            :value="systemConfig.gravity"
            min="-1000"
            max="1000"
            step="10"
            @input="updateSystemConfig('gravity', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ systemConfig.gravity }}</span>
        </div>
        <div class="property-row">
          <label title="Strength of the wind force applied to all particles. Creates directional drift.">Wind Strength</label>
          <input
            type="range"
            :value="systemConfig.windStrength"
            min="0"
            max="1000"
            step="10"
            @input="updateSystemConfig('windStrength', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ systemConfig.windStrength }}</span>
        </div>
        <div class="property-row">
          <label title="Direction of the wind in degrees. 0° = right, 90° = down, 180° = left, 270° = up.">Wind Direction</label>
          <input
            type="range"
            :value="systemConfig.windDirection"
            min="0"
            max="360"
            step="5"
            @input="updateSystemConfig('windDirection', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ systemConfig.windDirection }}°</span>
        </div>
        <div class="property-row">
          <label title="Air resistance that slows particles over time. 0 = no friction, 1 = maximum friction.">Friction</label>
          <input
            type="range"
            :value="systemConfig.friction"
            min="0"
            max="1"
            step="0.01"
            @input="updateSystemConfig('friction', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ systemConfig.friction.toFixed(2) }}</span>
        </div>
        <div class="property-row">
          <label title="What happens when particles hit the composition boundary. Kill = remove, Bounce = reflect, Wrap = appear on opposite side.">Boundary</label>
          <select
            :value="systemConfig.boundaryBehavior"
            @change="updateSystemConfig('boundaryBehavior', ($event.target as HTMLSelectElement).value)"
          >
            <option value="kill">Kill</option>
            <option value="bounce">Bounce</option>
            <option value="wrap">Wrap</option>
          </select>
        </div>
        <div class="property-row">
          <label title="Frames to pre-simulate before frame 0. Creates a 'steady state' effect where particles are already in motion at the start.">Warmup Period</label>
          <input
            type="range"
            :value="systemConfig.warmupPeriod"
            min="0"
            max="120"
            step="1"
            @input="updateSystemConfig('warmupPeriod', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ systemConfig.warmupPeriod }}f</span>
        </div>
        <div class="property-row checkbox-row">
          <label title="When enabled, particles will be confined within any mask applied to this layer.">
            <input
              type="checkbox"
              :checked="systemConfig.respectMaskBoundary"
              @change="updateSystemConfig('respectMaskBoundary', ($event.target as HTMLInputElement).checked)"
            />
            Respect Mask Boundary
          </label>
        </div>
        <div class="property-row checkbox-row gpu-row">
          <label title="Use WebGPU for hardware-accelerated particle simulation. Dramatically improves performance with high particle counts.">
            <input
              type="checkbox"
              :checked="systemConfig.useGPU"
              :disabled="!webgpuAvailable"
              @change="updateSystemConfig('useGPU', ($event.target as HTMLInputElement).checked)"
            />
            GPU Acceleration
            <span v-if="webgpuAvailable" class="gpu-status available">(WebGPU)</span>
            <span v-else class="gpu-status unavailable">(Not Available)</span>
          </label>
        </div>
      </div>
    </div>

    <!-- Emitters -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('emitters')">
        <i class="pi" :class="expandedSections.has('emitters') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Emitters</span>
        <button class="add-btn" @click.stop="addEmitter" title="Add Emitter">
          <i class="pi pi-plus" />
        </button>
      </div>
      <div v-if="expandedSections.has('emitters')" class="section-content">
        <div
          v-for="emitter in emitters"
          :key="emitter.id"
          class="emitter-item"
        >
          <div class="emitter-header" @click="toggleEmitter(emitter.id)">
            <i class="pi" :class="expandedEmitters.has(emitter.id) ? 'pi-chevron-down' : 'pi-chevron-right'" />
            <input
              type="text"
              :value="emitter.name"
              @input="updateEmitter(emitter.id, 'name', ($event.target as HTMLInputElement).value)"
              @click.stop
              class="emitter-name"
            />
            <label class="enabled-toggle">
              <input
                type="checkbox"
                :checked="emitter.enabled"
                @change="updateEmitter(emitter.id, 'enabled', ($event.target as HTMLInputElement).checked)"
                @click.stop
              />
            </label>
            <button class="remove-btn" @click.stop="removeEmitter(emitter.id)" title="Remove">
              <i class="pi pi-trash" />
            </button>
          </div>

          <div v-if="expandedEmitters.has(emitter.id)" class="emitter-content">
            <div class="property-row">
              <label title="Horizontal position of the emitter. 0 = left edge, 0.5 = center, 1 = right edge.">Position X</label>
              <input
                type="range"
                :value="emitter.x"
                min="0"
                max="1"
                step="0.01"
                @input="updateEmitter(emitter.id, 'x', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.x.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Vertical position of the emitter. 0 = top edge, 0.5 = center, 1 = bottom edge.">Position Y</label>
              <input
                type="range"
                :value="emitter.y"
                min="0"
                max="1"
                step="0.01"
                @input="updateEmitter(emitter.id, 'y', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.y.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Depth position of the emitter (CC Particle World Producer Z). Negative = closer to camera.">Position Z</label>
              <input
                type="range"
                :value="emitter.z ?? 0"
                min="-500"
                max="500"
                step="10"
                @input="updateEmitter(emitter.id, 'z', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.z ?? 0).toFixed(0) }}</span>
            </div>
            <div class="property-row">
              <label title="Primary emission direction in degrees. 0° = right, 90° = down, 180° = left, 270° = up.">Direction</label>
              <input
                type="range"
                :value="emitter.direction"
                min="0"
                max="360"
                step="5"
                @input="updateEmitter(emitter.id, 'direction', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.direction }}°</span>
            </div>
            <div class="property-row">
              <label title="Cone angle for particle emission. 0° = tight beam, 180° = hemisphere, 360° = full sphere.">Spread</label>
              <input
                type="range"
                :value="emitter.spread"
                min="0"
                max="360"
                step="5"
                @input="updateEmitter(emitter.id, 'spread', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.spread }}°</span>
            </div>
            <div class="property-row">
              <label title="Initial velocity of emitted particles in pixels per second.">Speed</label>
              <input
                type="range"
                :value="emitter.speed"
                min="1"
                max="1000"
                step="10"
                @input="updateEmitter(emitter.id, 'speed', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.speed }}</span>
            </div>
            <div class="property-row">
              <label title="Random variation in particle speed. Adds natural randomness to the emission.">Speed Variance</label>
              <input
                type="range"
                :value="emitter.speedVariance"
                min="0"
                max="500"
                step="10"
                @input="updateEmitter(emitter.id, 'speedVariance', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.speedVariance }}</span>
            </div>
            <div class="property-row">
              <label title="Diameter of each particle in pixels.">Size</label>
              <input
                type="range"
                :value="emitter.size"
                min="1"
                max="400"
                step="1"
                @input="updateEmitter(emitter.id, 'size', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.size }}px</span>
            </div>
            <div class="property-row">
              <label title="Random variation in particle size. Creates more natural-looking effects.">Size Variance</label>
              <input
                type="range"
                :value="emitter.sizeVariance"
                min="0"
                max="100"
                step="1"
                @input="updateEmitter(emitter.id, 'sizeVariance', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.sizeVariance }}</span>
            </div>
            <div class="property-row">
              <label title="Base color of particles when they spawn.">Color</label>
              <input
                type="color"
                :value="rgbToHex(emitter.color)"
                @input="updateEmitterColor(emitter.id, ($event.target as HTMLInputElement).value)"
              />
            </div>
            <div class="property-row">
              <label title="Number of particles spawned per second during continuous emission.">Emission Rate</label>
              <input
                type="range"
                :value="emitter.emissionRate"
                min="0.1"
                max="100"
                step="0.1"
                @input="updateEmitter(emitter.id, 'emissionRate', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.emissionRate.toFixed(1) }}/s</span>
            </div>
            <div class="property-row">
              <label title="How long each particle lives in frames (at 16fps: 16 frames = 1 second).">Lifetime</label>
              <input
                type="range"
                :value="emitter.particleLifetime"
                min="1"
                max="300"
                step="1"
                @input="updateEmitter(emitter.id, 'particleLifetime', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.particleLifetime }}f</span>
            </div>
            <div class="property-row">
              <label title="Percentage of max particles to spawn immediately at frame 0. Creates an instant 'explosion' of particles.">Initial Burst</label>
              <input
                type="range"
                :value="emitter.initialBurst"
                min="0"
                max="1"
                step="0.1"
                @input="updateEmitter(emitter.id, 'initialBurst', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.initialBurst * 100).toFixed(0) }}%</span>
            </div>
            <div class="property-row checkbox-row">
              <label title="Emit a burst of particles when audio beats are detected. Requires audio analysis.">
                <input
                  type="checkbox"
                  :checked="emitter.burstOnBeat"
                  @change="updateEmitter(emitter.id, 'burstOnBeat', ($event.target as HTMLInputElement).checked)"
                />
                Burst on Beat
              </label>
            </div>
            <div v-if="emitter.burstOnBeat" class="property-row">
              <label title="Number of particles to emit on each detected audio beat.">Burst Count</label>
              <input
                type="range"
                :value="emitter.burstCount"
                min="1"
                max="100"
                step="1"
                @input="updateEmitter(emitter.id, 'burstCount', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.burstCount }}</span>
            </div>

            <!-- Emitter Shape -->
            <div class="subsection-divider">Emitter Shape</div>
            <div class="property-row">
              <label title="Geometry from which particles are emitted. Point = single location, others distribute particles across the shape.">Shape</label>
              <select
                :value="emitter.shape || 'point'"
                @change="updateEmitter(emitter.id, 'shape', ($event.target as HTMLSelectElement).value)"
              >
                <option value="point">Point</option>
                <option value="line">Line</option>
                <option value="circle">Circle</option>
                <option value="box">Box</option>
                <option value="sphere">Sphere</option>
                <option value="cone">Cone</option>
                <option value="ring">Ring</option>
                <option value="spline">Spline Path</option>
                <option value="image">Image/Mask</option>
                <option value="depthEdge">Depth Edges</option>
              </select>
            </div>
            <div v-if="emitter.shape === 'circle' || emitter.shape === 'sphere' || emitter.shape === 'ring'" class="property-row">
              <label title="Outer radius of the emission shape as a fraction of composition size.">Radius</label>
              <input
                type="range"
                :value="emitter.shapeRadius || 0.1"
                min="0.01"
                max="0.5"
                step="0.01"
                @input="updateEmitter(emitter.id, 'shapeRadius', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.shapeRadius || 0.1).toFixed(2) }}</span>
            </div>
            <div v-if="emitter.shape === 'ring'" class="property-row">
              <label title="Inner radius of the ring. Particles emit in the area between inner and outer radius.">Inner Radius</label>
              <input
                type="range"
                :value="emitter.shapeInnerRadius || 0.05"
                min="0"
                max="0.4"
                step="0.01"
                @input="updateEmitter(emitter.id, 'shapeInnerRadius', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.shapeInnerRadius || 0.05).toFixed(2) }}</span>
            </div>
            <div v-if="emitter.shape === 'box'" class="property-row">
              <label title="Width of the box emission area as a fraction of composition width.">Width</label>
              <input
                type="range"
                :value="emitter.shapeWidth || 0.2"
                min="0.01"
                max="1"
                step="0.01"
                @input="updateEmitter(emitter.id, 'shapeWidth', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.shapeWidth || 0.2).toFixed(2) }}</span>
            </div>
            <div v-if="emitter.shape === 'box'" class="property-row">
              <label title="Height of the box emission area as a fraction of composition height.">Height</label>
              <input
                type="range"
                :value="emitter.shapeHeight || 0.2"
                min="0.01"
                max="1"
                step="0.01"
                @input="updateEmitter(emitter.id, 'shapeHeight', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.shapeHeight || 0.2).toFixed(2) }}</span>
            </div>
            <div v-if="emitter.shape === 'line'" class="property-row">
              <label title="Length of the line emission area as a fraction of composition size.">Length</label>
              <input
                type="range"
                :value="emitter.shapeWidth || 0.2"
                min="0.01"
                max="1"
                step="0.01"
                @input="updateEmitter(emitter.id, 'shapeWidth', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.shapeWidth || 0.2).toFixed(2) }}</span>
            </div>
            <div v-if="emitter.shape === 'cone'" class="property-row">
              <label title="Opening angle of the cone in degrees. 90° = hemisphere, 180° = full sphere.">Cone Angle</label>
              <input
                type="range"
                :value="emitter.coneAngle || 45"
                min="1"
                max="180"
                step="1"
                @input="updateEmitter(emitter.id, 'coneAngle', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ emitter.coneAngle || 45 }}°</span>
            </div>
            <div v-if="emitter.shape === 'cone'" class="property-row">
              <label title="Base radius of the cone as a fraction of composition size.">Cone Radius</label>
              <input
                type="range"
                :value="emitter.coneRadius || 0.1"
                min="0.01"
                max="0.5"
                step="0.01"
                @input="updateEmitter(emitter.id, 'coneRadius', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ (emitter.coneRadius || 0.1).toFixed(2) }}</span>
            </div>
            <!-- Spline Path emission controls -->
            <div v-if="emitter.shape === 'spline'" class="spline-emission-controls">
              <div class="property-row">
                <label title="Select a spline or path layer to emit particles along.">Path Layer</label>
                <select
                  :value="emitter.splinePath?.layerId || ''"
                  @change="updateEmitterSplinePath(emitter.id, 'layerId', ($event.target as HTMLSelectElement).value)"
                >
                  <option value="">Select path...</option>
                  <option 
                    v-for="layer in availableSplineLayers" 
                    :key="layer.id" 
                    :value="layer.id"
                  >
                    {{ layer.name }} ({{ layer.type }})
                  </option>
                </select>
              </div>
              <div class="property-row">
                <label title="How particles are distributed along the path.">Emit Mode</label>
                <select
                  :value="emitter.splinePath?.emitMode || 'random'"
                  @change="updateEmitterSplinePath(emitter.id, 'emitMode', ($event.target as HTMLSelectElement).value)"
                >
                  <option value="random">Random</option>
                  <option value="uniform">Uniform</option>
                  <option value="sequential">Sequential</option>
                  <option value="start">From Start</option>
                  <option value="end">From End</option>
                </select>
              </div>
              <div class="property-row checkbox-row">
                <label title="Align particle emission direction with the path tangent.">
                  <input
                    type="checkbox"
                    :checked="emitter.splinePath?.alignToPath ?? true"
                    @change="updateEmitterSplinePath(emitter.id, 'alignToPath', ($event.target as HTMLInputElement).checked)"
                  />
                  Align to Path
                </label>
              </div>
              <div class="property-row">
                <label title="Perpendicular offset from the path (positive = outward, negative = inward).">Offset</label>
                <input
                  type="range"
                  :value="emitter.splinePath?.offset || 0"
                  min="-100"
                  max="100"
                  step="1"
                  @input="updateEmitterSplinePath(emitter.id, 'offset', Number(($event.target as HTMLInputElement).value))"
                />
                <span class="value-display">{{ emitter.splinePath?.offset || 0 }}px</span>
              </div>
            </div>
            <!-- Image/Mask emission controls -->
            <div v-if="emitter.shape === 'image'" class="image-emission-controls">
              <div class="property-row">
                <label title="Select a layer to use as the emission mask. Particles emit from non-transparent pixels.">Source Layer</label>
                <select
                  :value="emitter.imageSourceLayerId || ''"
                  @change="updateEmitter(emitter.id, 'imageSourceLayerId', ($event.target as HTMLSelectElement).value || null)"
                >
                  <option value="">Select layer...</option>
                  <option v-for="layer in imageLayers" :key="layer.id" :value="layer.id">
                    {{ layer.name }}
                  </option>
                </select>
              </div>
              <div class="property-row">
                <label title="Minimum alpha value (0-1) for a pixel to be considered for emission.">Alpha Threshold</label>
                <input
                  type="range"
                  :value="emitter.emissionThreshold || 0.1"
                  min="0.01"
                  max="1"
                  step="0.01"
                  @input="updateEmitter(emitter.id, 'emissionThreshold', Number(($event.target as HTMLInputElement).value))"
                />
                <span class="value-display">{{ (emitter.emissionThreshold || 0.1).toFixed(2) }}</span>
              </div>
              <div class="property-row checkbox-row">
                <label title="Emit only from the edges of the masked area instead of filling it.">
                  <input
                    type="checkbox"
                    :checked="emitter.emitFromMaskEdge"
                    @change="updateEmitter(emitter.id, 'emitFromMaskEdge', ($event.target as HTMLInputElement).checked)"
                  />
                  Edge Detection
                </label>
              </div>
            </div>
            <!-- Depth Edge emission controls -->
            <div v-if="emitter.shape === 'depthEdge'" class="depth-emission-controls">
              <div class="property-row">
                <label title="Select a depth layer to use for edge detection. Particles emit from depth discontinuities (silhouette edges).">Depth Layer</label>
                <select
                  :value="emitter.depthSourceLayerId || ''"
                  @change="updateEmitter(emitter.id, 'depthSourceLayerId', ($event.target as HTMLSelectElement).value || null)"
                >
                  <option value="">Select depth layer...</option>
                  <option v-for="layer in depthLayers" :key="layer.id" :value="layer.id">
                    {{ layer.name }}
                  </option>
                </select>
              </div>
              <div class="property-row">
                <label title="Minimum depth gradient magnitude to be considered an edge. Lower = more edges detected.">Edge Threshold</label>
                <input
                  type="range"
                  :value="emitter.emissionThreshold || 0.05"
                  min="0.01"
                  max="0.5"
                  step="0.01"
                  @input="updateEmitter(emitter.id, 'emissionThreshold', Number(($event.target as HTMLInputElement).value))"
                />
                <span class="value-display">{{ (emitter.emissionThreshold || 0.05).toFixed(2) }}</span>
              </div>
              <div class="property-row">
                <label title="Scale factor for converting depth values to Z position. Higher = more 3D separation.">Depth Scale</label>
                <input
                  type="range"
                  :value="emitter.depthScale || 500"
                  min="0"
                  max="2000"
                  step="50"
                  @input="updateEmitter(emitter.id, 'depthScale', Number(($event.target as HTMLInputElement).value))"
                />
                <span class="value-display">{{ emitter.depthScale || 500 }}</span>
              </div>
            </div>
            <div v-if="emitter.shape !== 'point' && emitter.shape !== 'spline' && emitter.shape !== 'image' && emitter.shape !== 'depthEdge'" class="property-row checkbox-row">
              <label title="When enabled, particles only emit from the outline/edge of the shape instead of filling the entire area.">
                <input
                  type="checkbox"
                  :checked="emitter.emitFromEdge"
                  @change="updateEmitter(emitter.id, 'emitFromEdge', ($event.target as HTMLInputElement).checked)"
                />
                Emit from Edge Only
              </label>
            </div>
          </div>
        </div>

        <div v-if="emitters.length === 0" class="empty-message">
          No emitters. Click + to add one.
        </div>
      </div>
    </div>

    <!-- Force Fields -->
    <ParticleForceFieldsSection
      :gravity-wells="gravityWells"
      :vortices="vortices"
      :expanded="expandedSections.has('forces')"
      @toggle="toggleSection('forces')"
      @add-well="addGravityWell"
      @remove-well="removeGravityWell"
      @update-well="updateGravityWell"
      @add-vortex="addVortex"
      @remove-vortex="removeVortex"
      @update-vortex="updateVortex"
    />

    <!-- Turbulence Fields -->
    <ParticleTurbulenceSection
      :turbulence-fields="turbulenceFields"
      :expanded="expandedSections.has('turbulence')"
      @toggle="toggleSection('turbulence')"
      @add="addTurbulence"
      @remove="removeTurbulence"
      @update="updateTurbulence"
    />

    <!-- Flocking (Boids) Behavior -->
    <ParticleFlockingSection
      :flocking="flocking"
      :expanded="expandedSections.has('flocking')"
      @toggle="toggleSection('flocking')"
      @update="updateFlocking"
    />

    <!-- Collision Detection -->
    <ParticleCollisionSection
      :collision="collision"
      :expanded="expandedSections.has('collision')"
      @toggle="toggleSection('collision')"
      @update="updateCollision"
    />

    <!-- Collision Planes (Floor/Wall) -->
    <ParticleCollisionPlanesSection
      :planes="collisionPlanes"
      :expanded="expandedSections.has('collisionPlanes')"
      @toggle="toggleSection('collisionPlanes')"
      @add-plane="addCollisionPlane"
      @update-plane="updateCollisionPlane"
      @remove-plane="removeCollisionPlane"
    />

    <!-- Particle Groups -->
    <ParticleGroupsSection
      :groups="particleGroups"
      :expanded="expandedSections.has('particleGroups')"
      @toggle="toggleSection('particleGroups')"
      @add-group="addParticleGroup"
      @update-group="updateParticleGroup"
      @remove-group="removeParticleGroup"
    />

    <!-- Visualization (CC Particle World Style) -->
    <ParticleVisualizationSection
      :visualization="visualization"
      :expanded="expandedSections.has('visualization')"
      @toggle="toggleSection('visualization')"
      @update="updateVisualization"
    />

    <!-- Audio Bindings -->
    <ParticleAudioBindingsSection
      :audio-bindings="audioBindings"
      :expanded="expandedSections.has('audioBindings')"
      @toggle="toggleSection('audioBindings')"
      @add="addAudioBinding"
      @remove="removeAudioBinding"
      @update="updateAudioBinding"
    />

    <!-- Sub-Emitters -->
    <ParticleSubEmittersSection
      :sub-emitters="subEmitters"
      :emitters="emitters"
      :expanded="expandedSections.has('subEmitters')"
      @toggle="toggleSection('subEmitters')"
      @add="addSubEmitter"
      @remove="removeSubEmitter"
      @update="updateSubEmitter"
      @update-color="updateSubEmitterColor"
    />

    <!-- Modulations -->
    <ParticleModulationsSection
      :modulations="modulations"
      :emitters="emitters"
      :expanded="expandedSections.has('modulations')"
      @toggle="toggleSection('modulations')"
      @add="addModulation"
      @remove="removeModulation"
      @update="updateModulation"
    />

    <!-- Render Options -->
    <ParticleRenderSection
      :render-options="renderOptions"
      :connections="connections"
      :expanded="expandedSections.has('render')"
      @toggle="toggleSection('render')"
      @update="updateRenderOption"
      @update-connection="updateConnection"
    />

    <!-- Level of Detail (LOD) -->
    <ParticleLODSection
      :config="lodConfigForSection"
      :expanded="expandedSections.has('lod')"
      @toggle="toggleSection('lod')"
      @update="updateLODConfigFromSection"
    />

    <!-- Depth of Field (DOF) -->
    <ParticleDOFSection
      :config="dofConfigForSection"
      :expanded="expandedSections.has('dof')"
      @toggle="toggleSection('dof')"
      @update="updateDOFConfigFromSection"
    />

    <!-- Bake / Export Section -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('bake')">
        <i class="pi" :class="expandedSections.has('bake') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Bake &amp; Export</span>
      </div>
      <div v-if="expandedSections.has('bake')" class="section-content">
        <div class="bake-info">
          <p class="help-text">
            Bake particle simulation to keyframes or export trajectories for external tools.
          </p>
        </div>

        <div class="property-row">
          <label title="First frame to bake">Start Frame</label>
          <input
            type="number"
            v-model.number="bakeStartFrame"
            min="0"
            :max="bakeEndFrame"
          />
        </div>

        <div class="property-row">
          <label title="Last frame to bake">End Frame</label>
          <input
            type="number"
            v-model.number="bakeEndFrame"
            :min="bakeStartFrame"
          />
        </div>

        <div class="property-row">
          <label title="Maximum particles to track (for performance)">Max Particles</label>
          <input
            type="number"
            v-model.number="bakeMaxParticles"
            min="1"
            max="10000"
          />
        </div>

        <div class="property-row checkbox-row">
          <label>
            <input type="checkbox" v-model="bakeSimplify" />
            Simplify keyframes (reduce file size)
          </label>
        </div>

        <div class="bake-actions">
          <button
            class="bake-btn primary"
            @click="bakeToTrajectories"
            :disabled="isBaking"
            title="Export particle paths as JSON for 3D software"
          >
            <i class="pi" :class="isBaking ? 'pi-spinner pi-spin' : 'pi-download'" />
            {{ isBaking ? 'Baking...' : 'Export Trajectories' }}
          </button>

          <button
            class="bake-btn"
            @click="clearAndRebake"
            :disabled="isBaking"
            title="Clear cache and re-simulate"
          >
            <i class="pi pi-refresh" />
            Reset Simulation
          </button>
        </div>

        <div v-if="isBaking" class="bake-progress">
          <div class="progress-bar">
            <div class="progress-fill" :style="{ width: `${bakeProgress}%` }"></div>
          </div>
          <span class="progress-text">{{ bakeProgressText }}</span>
        </div>

        <div v-if="lastBakeResult" class="bake-result">
          <i class="pi pi-check-circle" />
          <span>Exported {{ lastBakeResult.totalParticles }} particles over {{ lastBakeResult.totalFrames }} frames</span>
        </div>
      </div>
    </div>

    <!-- Particle Count Display -->
    <div class="particle-count">
      <i class="pi pi-circle-fill" />
      <span>{{ particleCount }} particles</span>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, onMounted, ref, watch } from "vue";
import { ParticleGPUCompute } from "@/services/particleGPU";
import { useCompositorStore } from "@/stores/compositorStore";
import { usePresetStore } from "@/stores/presetStore";
import type { ParticlePreset } from "@/types/presets";
import ParticleLODSection from "./particle/ParticleLODSection.vue";
import ParticleDOFSection from "./particle/ParticleDOFSection.vue";
import ParticleCollisionPlanesSection from "./particle/ParticleCollisionPlanesSection.vue";
import ParticleGroupsSection from "./particle/ParticleGroupsSection.vue";
import type { CollisionPlane } from "./particle/ParticleCollisionPlanesSection.vue";
import type { ParticleGroup } from "./particle/ParticleGroupsSection.vue";
import type {
  AudioBindingConfig,
  CollisionConfig,
  ConnectionRenderConfig,
  FlockingConfig,
  GravityWellConfig,
  Layer,
  ParticleEmitterConfig,
  ParticleLayerData,
  ParticleModulationConfig,
  ParticleRenderOptions,
  ParticleSystemLayerConfig,
  SubEmitterConfig,
  TurbulenceFieldConfig,
  VortexConfig,
} from "@/types/project";

// Preset Store
const presetStore = usePresetStore();
presetStore.initialize();

// Compositor Store - for layer list
const compositorStore = useCompositorStore();

// Computed: Image layers for mask emission
const imageLayers = computed(() =>
  compositorStore.layers.filter(
    (l) => l.type === "image" || l.type === "video" || l.type === "solid",
  ),
);

// Computed: Depth layers for depth edge emission
const depthLayers = computed(() =>
  compositorStore.layers.filter(
    (l) =>
      l.type === "image" &&
      (l.name.toLowerCase().includes("depth") ||
        (l.data && "isDepthMap" in l.data && l.data.isDepthMap)),
  ),
);

// Computed: Spline and path layers for spline emission
const availableSplineLayers = computed(() =>
  compositorStore.layers.filter(
    (l) => l.type === "spline" || l.type === "path",
  ),
);

// WebGPU Detection
const webgpuAvailable = ref(false);

onMounted(async () => {
  webgpuAvailable.value = await ParticleGPUCompute.isAvailable();
});

// Preset UI State
const selectedPresetId = ref("");
const showSaveDialog = ref(false);
const newPresetName = ref("");
const newPresetDescription = ref("");
const newPresetTags = ref("");

// Computed preset lists
const builtInPresets = computed(() =>
  presetStore.particlePresets.filter((p) => p.isBuiltIn),
);
const userPresets = computed(() =>
  presetStore.particlePresets.filter((p) => !p.isBuiltIn),
);
const isBuiltInPreset = computed(() => {
  if (!selectedPresetId.value) return false;
  const preset = presetStore.getPreset(selectedPresetId.value);
  return preset?.isBuiltIn ?? false;
});

interface Props {
  layer: Layer;
  particleCount?: number;
}

const props = withDefaults(defineProps<Props>(), {
  particleCount: 0,
});

const emit =
  defineEmits<(e: "update", data: Partial<ParticleLayerData>) => void>();

// UI State - persist expanded sections per layer
const expandedSectionsMap = ref<Map<string, Set<string>>>(new Map());
const expandedEmittersMap = ref<Map<string, Set<string>>>(new Map());
const forceTab = ref<"wells" | "vortices">("wells");

// Get/set expanded sections for current layer
const expandedSections = computed({
  get: () => {
    const layerId = props.layer?.id;
    if (!layerId) return new Set(["system", "emitters"]);
    if (!expandedSectionsMap.value.has(layerId)) {
      expandedSectionsMap.value.set(layerId, new Set(["system", "emitters"]));
    }
    return expandedSectionsMap.value.get(layerId)!;
  },
  set: (val: Set<string>) => {
    const layerId = props.layer?.id;
    if (layerId) {
      expandedSectionsMap.value.set(layerId, val);
    }
  },
});

const expandedEmitters = computed({
  get: () => {
    const layerId = props.layer?.id;
    if (!layerId) return new Set<string>();
    if (!expandedEmittersMap.value.has(layerId)) {
      expandedEmittersMap.value.set(layerId, new Set<string>());
    }
    return expandedEmittersMap.value.get(layerId)!;
  },
  set: (val: Set<string>) => {
    const layerId = props.layer?.id;
    if (layerId) {
      expandedEmittersMap.value.set(layerId, val);
    }
  },
});

// Watch for layer changes to ensure UI stays in sync
watch(
  () => props.layer?.id,
  (newId, oldId) => {
    if (newId && newId !== oldId) {
      // Initialize expanded sections for new layer if not already set
      if (!expandedSectionsMap.value.has(newId)) {
        expandedSectionsMap.value.set(newId, new Set(["system", "emitters"]));
      }
      if (!expandedEmittersMap.value.has(newId)) {
        expandedEmittersMap.value.set(newId, new Set<string>());
      }
    }
  },
  { immediate: true },
);

// Deep watch for layer data changes to ensure computed properties update
watch(
  () => props.layer?.data,
  () => {
    // Force re-evaluation of computed properties when layer data changes externally
  },
  { deep: true },
);

// Get layer data with defaults
const layerData = computed((): ParticleLayerData => {
  const data = props.layer.data as ParticleLayerData | null;
  return (
    data || {
      systemConfig: {
        maxParticles: 10000,
        gravity: 0,
        windStrength: 0,
        windDirection: 0,
        warmupPeriod: 0,
        respectMaskBoundary: false,
        boundaryBehavior: "kill",
        friction: 0.01,
      },
      emitters: [],
      gravityWells: [],
      vortices: [],
      modulations: [],
      renderOptions: {
        blendMode: "additive",
        renderTrails: false,
        trailLength: 5,
        trailOpacityFalloff: 0.7,
        particleShape: "circle",
        glowEnabled: false,
        glowRadius: 10,
        glowIntensity: 0.5,
        motionBlur: false,
        motionBlurStrength: 0.5,
        motionBlurSamples: 8,
        connections: {
          enabled: false,
          maxDistance: 100,
          maxConnections: 3,
          lineWidth: 1,
          lineOpacity: 0.5,
          fadeByDistance: true,
        },
        // Sprite defaults
        spriteEnabled: false,
        spriteImageUrl: "",
        spriteColumns: 1,
        spriteRows: 1,
        spriteAnimate: false,
        spriteFrameRate: 10,
        spriteRandomStart: false,
      },
      turbulenceFields: [],
      subEmitters: [],
    }
  );
});

const systemConfig = computed(() => layerData.value.systemConfig);
const emitters = computed(() => layerData.value.emitters);
const gravityWells = computed(() => layerData.value.gravityWells);
const vortices = computed(() => layerData.value.vortices);
const modulations = computed(() => layerData.value.modulations);
const renderOptions = computed(() => layerData.value.renderOptions);
const turbulenceFields = computed(() => layerData.value.turbulenceFields || []);
const subEmitters = computed(() => layerData.value.subEmitters || []);

// Flocking config with defaults
const flocking = computed(
  () =>
    layerData.value.flocking || {
      enabled: false,
      separationWeight: 50,
      separationRadius: 25,
      alignmentWeight: 50,
      alignmentRadius: 50,
      cohesionWeight: 50,
      cohesionRadius: 50,
      maxSpeed: 200,
      maxForce: 10,
      perceptionAngle: 270,
    },
);

// Collision config with defaults
const collision = computed(
  () =>
    layerData.value.collision || {
      enabled: false,
      particleCollision: false,
      particleRadius: 5,
      bounciness: 0.5,
      friction: 0.1,
      boundaryEnabled: false,
      boundaryBehavior: "bounce" as const,
      boundaryPadding: 0,
    },
);

const connections = computed(
  () =>
    renderOptions.value.connections || {
      enabled: false,
      maxDistance: 100,
      maxConnections: 3,
      lineWidth: 1,
      lineOpacity: 0.5,
      fadeByDistance: true,
    },
);
const audioBindings = computed(() => layerData.value.audioBindings || []);
const particleCount = computed(() => props.particleCount);

// LOD config with defaults
const lodConfig = computed(() =>
  layerData.value.lodConfig || {
    enabled: false,
    distances: [100, 300, 600],
    sizeMultipliers: [1.0, 0.5, 0.25],
  },
);

// DOF config with defaults
const dofConfig = computed(() =>
  layerData.value.dofConfig || {
    enabled: false,
    focusDistance: 500,
    focusRange: 200,
    blurAmount: 0.5,
  },
);

// Collision planes with defaults
const collisionPlanes = computed((): CollisionPlane[] =>
  layerData.value.collisionPlanes || [],
);

// Particle groups with defaults
const particleGroups = computed((): ParticleGroup[] =>
  layerData.value.particleGroups || [
    {
      id: "default",
      name: "Default",
      enabled: true,
      color: [1, 1, 1, 1] as [number, number, number, number],
      collisionMask: 0b11111111,
      connectionMask: 0b11111111,
    },
  ],
);

// Visualization settings (CC Particle World style)
const visualization = computed(
  () =>
    layerData.value.visualization || {
      showHorizon: false,
      showGrid: false,
      showAxis: false,
      gridSize: 100,
      gridDepth: 500,
    },
);

// Adapter for LOD section component (transforms internal format to component's expected format)
import type { LODConfig } from "./particle/ParticleLODSection.vue";
import type { DOFConfig } from "./particle/ParticleDOFSection.vue";

const lodConfigForSection = computed<LODConfig>(() => ({
  enabled: lodConfig.value.enabled,
  nearDistance: lodConfig.value.distances[0] ?? 100,
  midDistance: lodConfig.value.distances[1] ?? 300,
  farDistance: lodConfig.value.distances[2] ?? 600,
  nearSizeMultiplier: lodConfig.value.sizeMultipliers[0] ?? 1.0,
  midSizeMultiplier: lodConfig.value.sizeMultipliers[1] ?? 0.5,
  farSizeMultiplier: lodConfig.value.sizeMultipliers[2] ?? 0.25,
}));

const dofConfigForSection = computed<DOFConfig>(() => ({
  enabled: dofConfig.value.enabled,
  focusDistance: dofConfig.value.focusDistance,
  focusRange: dofConfig.value.focusRange,
  maxBlur: dofConfig.value.blurAmount,
}));

function updateLODConfigFromSection(key: keyof LODConfig, value: number | boolean): void {
  const distances = [...lodConfig.value.distances];
  const sizeMultipliers = [...lodConfig.value.sizeMultipliers];
  let enabled = lodConfig.value.enabled;

  if (key === "enabled") {
    enabled = value as boolean;
  } else if (key === "nearDistance") {
    distances[0] = value as number;
  } else if (key === "midDistance") {
    distances[1] = value as number;
  } else if (key === "farDistance") {
    distances[2] = value as number;
  } else if (key === "nearSizeMultiplier") {
    sizeMultipliers[0] = value as number;
  } else if (key === "midSizeMultiplier") {
    sizeMultipliers[1] = value as number;
  } else if (key === "farSizeMultiplier") {
    sizeMultipliers[2] = value as number;
  }
  emit("update", { lodConfig: { enabled, distances, sizeMultipliers } });
}

function updateDOFConfigFromSection(key: keyof DOFConfig, value: number | boolean): void {
  const updated = { ...dofConfig.value };
  if (key === "enabled") {
    updated.enabled = value as boolean;
  } else if (key === "focusDistance") {
    updated.focusDistance = value as number;
  } else if (key === "focusRange") {
    updated.focusRange = value as number;
  } else if (key === "maxBlur") {
    updated.blurAmount = value as number;
  }
  emit("update", { dofConfig: updated });
}

// Section toggle - using new Set to trigger reactivity
function toggleSection(section: string): void {
  const current = expandedSections.value;
  const newSet = new Set(current);
  if (newSet.has(section)) {
    newSet.delete(section);
  } else {
    newSet.add(section);
  }
  expandedSections.value = newSet;
}

function toggleEmitter(id: string): void {
  const current = expandedEmitters.value;
  const newSet = new Set(current);
  if (newSet.has(id)) {
    newSet.delete(id);
  } else {
    newSet.add(id);
  }
  expandedEmitters.value = newSet;
}

// Preset functions
function applySelectedPreset(): void {
  if (!selectedPresetId.value) return;

  const preset = presetStore.getPreset(selectedPresetId.value) as
    | ParticlePreset
    | undefined;
  if (!preset || preset.category !== "particle") return;

  // Merge preset config with current data
  const config = preset.config;
  const updates: Partial<ParticleLayerData> = {};

  if (config.maxParticles !== undefined) {
    updates.systemConfig = {
      ...systemConfig.value,
      maxParticles: config.maxParticles,
    };
  }

  // Apply gravity if specified
  if (config.gravity !== undefined) {
    // Handle gravity as either a number or an object with y property
    const gravityValue =
      typeof config.gravity === "number"
        ? config.gravity
        : ((config.gravity as { y?: number })?.y ?? 0);
    updates.systemConfig = {
      ...(updates.systemConfig || systemConfig.value),
      gravity: gravityValue,
    };
  }

  // Apply emitter defaults if specified
  if (
    config.emissionRate ||
    config.lifespan ||
    config.startSize ||
    config.endSize
  ) {
    const defaultEmitter = emitters.value[0] || createDefaultEmitter();
    updates.emitters = [
      {
        ...defaultEmitter,
        emissionRate: config.emissionRate ?? defaultEmitter.emissionRate,
        lifespan: config.lifespan ?? defaultEmitter.lifespan,
        startSize: config.startSize ?? defaultEmitter.startSize,
        endSize: config.endSize ?? defaultEmitter.endSize,
        startColor: config.startColor ?? defaultEmitter.startColor,
        endColor: config.endColor ?? defaultEmitter.endColor,
        velocitySpread: config.velocitySpread ?? defaultEmitter.velocitySpread,
      },
    ];
  }

  // Apply turbulence if specified
  if (config.turbulenceStrength !== undefined) {
    updates.turbulenceFields = [
      {
        id: "turbulence-from-preset",
        enabled: true,
        strength: config.turbulenceStrength,
        scale: 0.01,
        evolutionSpeed: 1, // Required field
        octaves: 3,
        persistence: 0.5,
        animationSpeed: 1,
      },
    ];
  }

  emit("update", updates);
}

function createDefaultEmitter(): ParticleEmitterConfig {
  return {
    id: `emitter_${Date.now()}`,
    name: "New Emitter",
    x: 0.5,
    y: 0.5,
    direction: 270, // degrees, upward
    spread: 30,
    speed: 100,
    speedVariance: 30,
    size: 10,
    sizeVariance: 2,
    color: [255, 255, 255],
    emissionRate: 50,
    initialBurst: 0,
    particleLifetime: 60,
    lifetimeVariance: 10,
    enabled: true,
    burstOnBeat: false,
    burstCount: 10,
    // Shape properties
    shape: "point",
    shapeRadius: 0,
    shapeWidth: 0,
    shapeHeight: 0,
    shapeDepth: 0,
    shapeInnerRadius: 0,
    emitFromEdge: false,
    emitFromVolume: false,
    splinePath: null,
    // Sprite config
    sprite: {
      enabled: false,
      imageUrl: null,
      imageData: null,
      isSheet: false,
      columns: 1,
      rows: 1,
      totalFrames: 1,
      frameRate: 30,
      playMode: "loop",
      billboard: false,
      rotationEnabled: false,
      rotationSpeed: 0,
      rotationSpeedVariance: 0,
      alignToVelocity: false,
    },
    // Alternative property names for preset compatibility
    lifespan: 2,
    startSize: 10,
    endSize: 2,
    startColor: "#ffffff",
    endColor: "#ffffff",
    startOpacity: 1,
    endOpacity: 0,
    velocitySpread: 30,
  };
}

function saveCurrentAsPreset(): void {
  if (!newPresetName.value.trim()) return;

  const tags = newPresetTags.value
    .split(",")
    .map((t) => t.trim())
    .filter((t) => t.length > 0);

  // Extract current config
  const emitter = emitters.value[0];
  const turbulence = turbulenceFields.value[0];

  presetStore.saveParticlePreset(
    newPresetName.value.trim(),
    {
      maxParticles: systemConfig.value.maxParticles,
      emissionRate: emitter?.emissionRate,
      lifespan: emitter?.lifespan,
      startSize: emitter?.startSize,
      endSize: emitter?.endSize,
      startColor: emitter?.startColor,
      endColor: emitter?.endColor,
      gravity: systemConfig.value.gravity,
      turbulenceStrength: turbulence?.strength,
      velocitySpread: emitter?.velocitySpread,
    },
    {
      description: newPresetDescription.value.trim() || undefined,
      tags: tags.length > 0 ? tags : undefined,
    },
  );

  // Reset dialog
  showSaveDialog.value = false;
  newPresetName.value = "";
  newPresetDescription.value = "";
  newPresetTags.value = "";
}

function deleteSelectedPreset(): void {
  if (!selectedPresetId.value || isBuiltInPreset.value) return;

  if (confirm("Delete this preset?")) {
    presetStore.deletePreset(selectedPresetId.value);
    selectedPresetId.value = "";
  }
}

// Update functions
function updateSystemConfig(
  key: keyof ParticleSystemLayerConfig,
  value: any,
): void {
  emit("update", {
    systemConfig: { ...systemConfig.value, [key]: value },
  });
}

function updateEmitter(
  id: string,
  key: keyof ParticleEmitterConfig,
  value: any,
): void {
  const updated = emitters.value.map((e) =>
    e.id === id ? { ...e, [key]: value } : e,
  );
  emit("update", { emitters: updated });
}

function updateEmitterColor(id: string, hex: string): void {
  const rgb = hexToRgb(hex);
  updateEmitter(id, "color", rgb);
}

// Update spline path emission settings
function updateEmitterSplinePath(
  emitterId: string,
  key: string,
  value: any,
): void {
  const emitter = emitters.value.find((e) => e.id === emitterId);
  if (!emitter) return;

  // Create or update the splinePath object
  const currentSplinePath = emitter.splinePath || {
    layerId: "",
    emitMode: "random" as const,
    parameter: 0,
    alignToPath: true,
    offset: 0,
    bidirectional: false,
  };

  const updatedSplinePath = {
    ...currentSplinePath,
    [key]: value,
  };

  const updated = emitters.value.map((e) =>
    e.id === emitterId ? { ...e, splinePath: updatedSplinePath } : e,
  );
  emit("update", { emitters: updated });
}

function addEmitter(): void {
  const newEmitter: ParticleEmitterConfig = {
    id: `emitter_${Date.now()}`,
    name: `Emitter ${emitters.value.length + 1}`,
    x: 0.5,
    y: 0.5,
    direction: 270,
    spread: 30,
    speed: 330,
    speedVariance: 50,
    size: 17,
    sizeVariance: 5,
    color: [255, 255, 255],
    emissionRate: 10,
    initialBurst: 0,
    particleLifetime: 60,
    lifetimeVariance: 10,
    enabled: true,
    burstOnBeat: false,
    burstCount: 20,
    // Shape properties
    shape: "point",
    shapeRadius: 0,
    shapeWidth: 0,
    shapeHeight: 0,
    shapeDepth: 0,
    shapeInnerRadius: 0,
    emitFromEdge: false,
    emitFromVolume: false,
    splinePath: null,
    // Sprite config
    sprite: {
      enabled: false,
      imageUrl: null,
      imageData: null,
      isSheet: false,
      columns: 1,
      rows: 1,
      totalFrames: 1,
      frameRate: 30,
      playMode: "loop",
      billboard: false,
      rotationEnabled: false,
      rotationSpeed: 0,
      rotationSpeedVariance: 0,
      alignToVelocity: false,
    },
  };
  emit("update", { emitters: [...emitters.value, newEmitter] });
  expandedEmitters.value.add(newEmitter.id);
}

function removeEmitter(id: string): void {
  emit("update", { emitters: emitters.value.filter((e) => e.id !== id) });
}

function updateGravityWell(
  id: string,
  key: keyof GravityWellConfig,
  value: any,
): void {
  const updated = gravityWells.value.map((w) =>
    w.id === id ? { ...w, [key]: value } : w,
  );
  emit("update", { gravityWells: updated });
}

function addGravityWell(): void {
  const newWell: GravityWellConfig = {
    id: `well_${Date.now()}`,
    name: `Gravity Well ${gravityWells.value.length + 1}`,
    x: 0.5,
    y: 0.5,
    strength: 100,
    radius: 0.3,
    falloff: "quadratic",
    enabled: true,
  };
  emit("update", { gravityWells: [...gravityWells.value, newWell] });
}

function removeGravityWell(id: string): void {
  emit("update", {
    gravityWells: gravityWells.value.filter((w) => w.id !== id),
  });
}

function updateVortex(id: string, key: keyof VortexConfig, value: any): void {
  const updated = vortices.value.map((v) =>
    v.id === id ? { ...v, [key]: value } : v,
  );
  emit("update", { vortices: updated });
}

function addVortex(): void {
  const newVortex: VortexConfig = {
    id: `vortex_${Date.now()}`,
    name: `Vortex ${vortices.value.length + 1}`,
    x: 0.5,
    y: 0.5,
    strength: 200,
    radius: 0.3,
    rotationSpeed: 5,
    inwardPull: 10,
    enabled: true,
  };
  emit("update", { vortices: [...vortices.value, newVortex] });
}

function removeVortex(id: string): void {
  emit("update", { vortices: vortices.value.filter((v) => v.id !== id) });
}

function updateModulation(
  id: string,
  key: keyof ParticleModulationConfig,
  value: any,
): void {
  const updated = modulations.value.map((m) =>
    m.id === id ? { ...m, [key]: value } : m,
  );
  emit("update", { modulations: updated });
}

function addModulation(): void {
  const newMod: ParticleModulationConfig = {
    id: `mod_${Date.now()}`,
    emitterId: "*",
    property: "opacity",
    startValue: 1,
    endValue: 0,
    easing: "linear",
  };
  emit("update", { modulations: [...modulations.value, newMod] });
}

function removeModulation(id: string): void {
  emit("update", { modulations: modulations.value.filter((m) => m.id !== id) });
}

function updateRenderOption(
  key: keyof ParticleRenderOptions,
  value: any,
): void {
  emit("update", {
    renderOptions: { ...renderOptions.value, [key]: value },
  });
}

// Connection functions
function updateConnection(
  key: keyof ConnectionRenderConfig,
  value: any,
): void {
  emit("update", {
    renderOptions: {
      ...renderOptions.value,
      connections: { ...connections.value, [key]: value },
    },
  });
}

// Turbulence functions
function updateTurbulence(
  id: string,
  key: keyof TurbulenceFieldConfig,
  value: any,
): void {
  const updated = turbulenceFields.value.map((t) =>
    t.id === id ? { ...t, [key]: value } : t,
  );
  emit("update", { turbulenceFields: updated });
}

function addTurbulence(): void {
  const newTurb: TurbulenceFieldConfig = {
    id: `turb_${Date.now()}`,
    enabled: true,
    scale: 0.005,
    strength: 100,
    evolutionSpeed: 0.1,
  };
  emit("update", { turbulenceFields: [...turbulenceFields.value, newTurb] });
}

function removeTurbulence(id: string): void {
  emit("update", {
    turbulenceFields: turbulenceFields.value.filter((t) => t.id !== id),
  });
}

// Flocking functions
function updateFlocking(key: keyof FlockingConfig, value: any): void {
  emit("update", {
    flocking: { ...flocking.value, [key]: value },
  });
}

// Collision functions
function updateCollision(key: keyof CollisionConfig, value: any): void {
  emit("update", {
    collision: { ...collision.value, [key]: value },
  });
}

// Visualization functions (CC Particle World style)
interface VisualizationConfig {
  showHorizon: boolean;
  showGrid: boolean;
  showAxis: boolean;
  gridSize: number;
  gridDepth: number;
}

function updateVisualization(
  key: keyof VisualizationConfig,
  value: any,
): void {
  emit("update", {
    visualization: { ...visualization.value, [key]: value },
  });
}

// Audio binding functions
function addAudioBinding(): void {
  const newBinding: AudioBindingConfig = {
    id: `audio_${Date.now()}`,
    enabled: true,
    feature: "amplitude",
    smoothing: 0.3,
    min: 0,
    max: 1,
    target: "emitter",
    targetId: emitters.value[0]?.id || "",
    parameter: "emissionRate",
    outputMin: 1,
    outputMax: 50,
    curve: "linear",
    stepCount: 5,
    triggerMode: "continuous",
    threshold: 0.5,
  };
  emit("update", { audioBindings: [...audioBindings.value, newBinding] });
}

function updateAudioBinding(
  id: string,
  key: keyof AudioBindingConfig,
  value: any,
): void {
  const updated = audioBindings.value.map((b) =>
    b.id === id ? { ...b, [key]: value } : b,
  );
  emit("update", { audioBindings: updated });
}

function removeAudioBinding(id: string): void {
  emit("update", {
    audioBindings: audioBindings.value.filter((b) => b.id !== id),
  });
}

// Sub-emitter functions
function updateSubEmitter(
  id: string,
  key: keyof SubEmitterConfig,
  value: any,
): void {
  const updated = subEmitters.value.map((s) =>
    s.id === id ? { ...s, [key]: value } : s,
  );
  emit("update", { subEmitters: updated });
}

function updateSubEmitterColor(id: string, hex: string): void {
  const rgb = hexToRgb(hex);
  updateSubEmitter(id, "color", rgb);
}

function addSubEmitter(): void {
  const newSub: SubEmitterConfig = {
    id: `sub_${Date.now()}`,
    parentEmitterId: "*",
    trigger: "death",
    spawnCount: 3,
    inheritVelocity: 0.5,
    size: 5,
    sizeVariance: 2,
    lifetime: 30,
    speed: 50,
    spread: 360,
    color: [255, 200, 100],
    enabled: true,
  };
  emit("update", { subEmitters: [...subEmitters.value, newSub] });
}

function removeSubEmitter(id: string): void {
  emit("update", { subEmitters: subEmitters.value.filter((s) => s.id !== id) });
}

// LOD functions
function updateLODConfig(key: string, value: boolean | number[]): void {
  const updated = { ...lodConfig.value };
  if (key === "enabled") {
    updated.enabled = value as boolean;
  } else if (key === "distances") {
    updated.distances = value as number[];
  } else if (key === "sizeMultipliers") {
    updated.sizeMultipliers = value as number[];
  }
  emit("update", { lodConfig: updated });
}

// DOF functions
function updateDOFConfig(key: string, value: boolean | number): void {
  const updated = { ...dofConfig.value };
  if (key === "enabled") {
    updated.enabled = value as boolean;
  } else if (key === "focusDistance") {
    updated.focusDistance = value as number;
  } else if (key === "focusRange") {
    updated.focusRange = value as number;
  } else if (key === "blurAmount") {
    updated.blurAmount = value as number;
  }
  emit("update", { dofConfig: updated });
}

// Collision Planes functions
function addCollisionPlane(type: string): void {
  const id = `plane_${Date.now()}`;
  let plane: CollisionPlane;

  switch (type) {
    case "floor":
      plane = {
        id,
        name: "Floor",
        enabled: true,
        point: { x: 0, y: 0, z: 0 },
        normal: { x: 0, y: 1, z: 0 },
        bounciness: 0.5,
        friction: 0.3,
      };
      break;
    case "ceiling":
      plane = {
        id,
        name: "Ceiling",
        enabled: true,
        point: { x: 0, y: 500, z: 0 },
        normal: { x: 0, y: -1, z: 0 },
        bounciness: 0.5,
        friction: 0.3,
      };
      break;
    case "wall-left":
      plane = {
        id,
        name: "Left Wall",
        enabled: true,
        point: { x: -500, y: 0, z: 0 },
        normal: { x: 1, y: 0, z: 0 },
        bounciness: 0.5,
        friction: 0.3,
      };
      break;
    case "wall-right":
      plane = {
        id,
        name: "Right Wall",
        enabled: true,
        point: { x: 500, y: 0, z: 0 },
        normal: { x: -1, y: 0, z: 0 },
        bounciness: 0.5,
        friction: 0.3,
      };
      break;
    default:
      plane = {
        id,
        name: "Plane",
        enabled: true,
        point: { x: 0, y: 0, z: 0 },
        normal: { x: 0, y: 1, z: 0 },
        bounciness: 0.5,
        friction: 0.3,
      };
  }

  emit("update", { collisionPlanes: [...collisionPlanes.value, plane] });
}

function updateCollisionPlane(
  id: string,
  key: string,
  value: boolean | number | { x: number; y: number; z: number },
): void {
  const updated = collisionPlanes.value.map((p) =>
    p.id === id ? { ...p, [key]: value } : p,
  );
  emit("update", { collisionPlanes: updated });
}

function removeCollisionPlane(id: string): void {
  emit("update", {
    collisionPlanes: collisionPlanes.value.filter((p) => p.id !== id),
  });
}

// Particle Groups functions
function addParticleGroup(): void {
  const id = `group_${Date.now()}`;
  const groupIndex = particleGroups.value.length;

  const newGroup: ParticleGroup = {
    id,
    name: `Group ${groupIndex + 1}`,
    enabled: true,
    color: [Math.random(), Math.random(), Math.random(), 1] as [number, number, number, number],
    collisionMask: 0b11111111, // Collide with all by default
    connectionMask: 0b11111111, // Connect with all by default
  };

  emit("update", { particleGroups: [...particleGroups.value, newGroup] });
}

function updateParticleGroup(
  id: string,
  key: string,
  value: string | number | boolean | [number, number, number, number],
): void {
  const updated = particleGroups.value.map((g) =>
    g.id === id ? { ...g, [key]: value } : g,
  );
  emit("update", { particleGroups: updated });
}

function removeParticleGroup(id: string): void {
  // Cannot remove the default group
  if (id === "default") return;

  emit("update", {
    particleGroups: particleGroups.value.filter((g) => g.id !== id),
  });
}

// Color utilities
function rgbToHex(rgb: [number, number, number]): string {
  return `#${rgb.map((c) => c.toString(16).padStart(2, "0")).join("")}`;
}

function hexToRgb(hex: string): [number, number, number] {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  return result
    ? [
        parseInt(result[1], 16),
        parseInt(result[2], 16),
        parseInt(result[3], 16),
      ]
    : [255, 255, 255];
}

// ============================================================================
// BAKE TO KEYFRAMES / TRAJECTORY EXPORT
// ============================================================================

import {
  exportTrajectoriesToJSON,
  type ParticleBakeResult,
} from "@/stores/actions/particleLayerActions";

// Bake state
const bakeStartFrame = ref(0);
const bakeEndFrame = ref(80);
const bakeMaxParticles = ref(1000);
const bakeSimplify = ref(true);
const isBaking = ref(false);
const bakeProgress = ref(0);
const bakeProgressText = ref("");
const lastBakeResult = ref<ParticleBakeResult | null>(null);

/**
 * Export particle trajectories as JSON
 * This captures all particle paths over the frame range
 */
async function bakeToTrajectories(): Promise<void> {
  if (isBaking.value) return;

  isBaking.value = true;
  bakeProgress.value = 0;
  bakeProgressText.value = "Starting...";
  lastBakeResult.value = null;

  try {
    // Get the particle layer instance from the engine
    const engine = (window as any).__latticeEngine;
    if (!engine) {
      throw new Error("Engine not available");
    }

    const particleLayer = engine.getLayer(props.layer.id);
    if (!particleLayer || !("exportTrajectories" in particleLayer)) {
      throw new Error("Particle layer not found or doesn't support export");
    }

    // Export trajectories
    const trajectoryData = await particleLayer.exportTrajectories(
      bakeStartFrame.value,
      bakeEndFrame.value,
      (frame: number, total: number) => {
        bakeProgress.value = Math.round((frame / total) * 100);
        bakeProgressText.value = `Processing frame ${frame} / ${total}`;
      },
    );

    // Convert to baked trajectories format
    const particleLifetimes = new Map<number, { birth: number; death: number; keyframes: any[] }>();

    // Process each frame's particles
    for (const [frame, particles] of trajectoryData) {
      for (const p of particles) {
        if (!particleLifetimes.has(p.id)) {
          particleLifetimes.set(p.id, {
            birth: frame,
            death: frame,
            keyframes: [],
          });
        }

        const lifetime = particleLifetimes.get(p.id)!;
        lifetime.death = frame;
        lifetime.keyframes.push({
          frame,
          x: p.x,
          y: p.y,
          z: p.z,
          size: p.size,
          opacity: p.opacity,
          rotation: p.rotation,
          r: p.r,
          g: p.g,
          b: p.b,
        });
      }
    }

    // Convert to result format
    const trajectories = Array.from(particleLifetimes.entries())
      .slice(0, bakeMaxParticles.value)
      .map(([id, data]) => ({
        particleId: id,
        emitterId: "default",
        birthFrame: data.birth,
        deathFrame: data.death,
        keyframes: data.keyframes,
      }));

    const result: ParticleBakeResult = {
      layerId: props.layer.id,
      trajectories,
      totalFrames: bakeEndFrame.value - bakeStartFrame.value + 1,
      totalParticles: trajectories.length,
      exportFormat: "trajectories",
    };

    lastBakeResult.value = result;

    // Export as JSON file
    const json = exportTrajectoriesToJSON(result);
    const blob = new Blob([json], { type: "application/json" });
    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `particle_trajectories_${props.layer.name || "layer"}.json`;
    a.click();
    URL.revokeObjectURL(url);

    bakeProgressText.value = "Export complete!";
  } catch (error) {
    console.error("Bake failed:", error);
    bakeProgressText.value = `Error: ${error instanceof Error ? error.message : "Unknown error"}`;
  } finally {
    isBaking.value = false;
  }
}

/**
 * Clear cache and reset simulation
 */
function clearAndRebake(): void {
  const engine = (window as any).__latticeEngine;
  if (!engine) return;

  const particleLayer = engine.getLayer(props.layer.id);
  if (particleLayer && "clearCache" in particleLayer) {
    (particleLayer as any).clearCache();
  }

  lastBakeResult.value = null;
  bakeProgressText.value = "Cache cleared";
}
</script>

<style scoped>
.particle-properties {
  font-size: 12px;
}

.property-section {
  border-bottom: 1px solid #333;
}

.section-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px;
  cursor: pointer;
  background: #2d2d2d;
  font-weight: 500;
}

.section-header:hover {
  background: #333;
}

.section-header i {
  font-size: 12px;
  width: 14px;
}

.section-header .add-btn {
  margin-left: auto;
  padding: 2px 6px;
  border: none;
  background: transparent;
  color: #888;
  cursor: pointer;
}

.section-header .add-btn:hover {
  color: #4a90d9;
}

.section-content {
  padding: 8px;
  background: #252525;
}

.subsection-label {
  font-size: 11px;
  font-weight: 600;
  color: #6a6a6a;
  text-transform: uppercase;
  letter-spacing: 0.5px;
  margin: 12px 0 6px 0;
  padding-bottom: 4px;
  border-bottom: 1px solid #333;
}

.subsection-label:first-child {
  margin-top: 4px;
}

.property-row {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-bottom: 8px;
}

.property-row label {
  width: 90px;
  flex-shrink: 0;
  color: #888;
  font-size: 13px;
}

.property-row input[type="range"] {
  flex: 1;
  min-width: 60px;
}

.property-row input[type="number"],
.property-row input[type="text"],
.property-row select {
  flex: 1;
  padding: 4px 6px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}

.property-row input[type="color"] {
  width: 40px;
  height: 24px;
  padding: 0;
  border: 1px solid #3d3d3d;
  border-radius: 3px;
}

.value-display {
  width: 50px;
  text-align: right;
  font-variant-numeric: tabular-nums;
  color: #aaa;
  font-size: 12px;
}

.checkbox-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  width: auto;
  cursor: pointer;
}

.emitter-item,
.force-item,
.modulation-item {
  background: #1e1e1e;
  border-radius: 4px;
  margin-bottom: 8px;
  overflow: hidden;
}

.emitter-header,
.force-header,
.modulation-header {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 6px 8px;
  background: #2a2a2a;
  cursor: pointer;
}

.emitter-header i {
  font-size: 12px;
  color: #666;
}

.emitter-name,
.force-name {
  flex: 1;
  padding: 2px 4px;
  border: 1px solid transparent;
  background: transparent;
  color: #e0e0e0;
  font-size: 13px;
}

.emitter-name:focus,
.force-name:focus {
  border-color: #4a90d9;
  background: #1e1e1e;
  outline: none;
}

.enabled-toggle {
  display: flex;
  align-items: center;
}

.enabled-toggle input {
  margin: 0;
}

.remove-btn {
  padding: 2px 6px;
  border: none;
  background: transparent;
  color: #666;
  cursor: pointer;
}

.remove-btn:hover {
  color: #e55;
}

.emitter-content {
  padding: 8px;
}

.force-tabs {
  display: flex;
  gap: 4px;
  margin-bottom: 8px;
}

.force-tabs button {
  flex: 1;
  padding: 6px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #888;
  border-radius: 3px;
  font-size: 13px;
  cursor: pointer;
}

.force-tabs button.active {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.force-list {
  max-height: 300px;
  overflow-y: auto;
}

.add-btn.full-width {
  width: 100%;
  padding: 8px;
  margin-bottom: 8px;
  border: 1px dashed #3d3d3d;
  background: transparent;
  color: #888;
  border-radius: 4px;
  cursor: pointer;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
}

.add-btn.full-width:hover {
  border-color: #4a90d9;
  color: #4a90d9;
}

.empty-message {
  padding: 12px;
  text-align: center;
  color: #666;
  font-style: italic;
}

.particle-count {
  display: flex;
  align-items: center;
  gap: 6px;
  padding: 8px 12px;
  background: #2d2d2d;
  color: #888;
  font-size: 13px;
}

.particle-count i {
  font-size: 11px;
  color: #4a90d9;
}

.subsection-divider {
  margin: 12px 0 8px;
  padding: 6px 0;
  border-top: 1px solid #3d3d3d;
  font-size: 13px;
  color: #888;
  font-weight: 500;
}

.force-label {
  flex: 1;
  font-size: 13px;
  color: #aaa;
}

.sub-emitter-parent {
  flex: 1;
  padding: 2px 4px;
  border: 1px solid #3d3d3d;
  background: #1e1e1e;
  color: #e0e0e0;
  border-radius: 3px;
  font-size: 13px;
}

/* Preset Styles */
.presets-section {
  border-bottom: 2px solid #4a90d9;
}

.preset-controls {
  display: flex;
  gap: 6px;
  margin-bottom: 8px;
}

.preset-select {
  flex: 1;
  padding: 6px 8px;
  background: #1e1e1e;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.preset-select:focus {
  outline: none;
  border-color: #4a90d9;
}

.preset-actions {
  display: flex;
  gap: 6px;
}

.preset-btn {
  padding: 6px 12px;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  background: #2d2d2d;
  color: #e0e0e0;
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s;
}

.preset-btn:hover:not(:disabled) {
  background: #3d3d3d;
}

.preset-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.preset-btn.apply {
  background: #4a90d9;
  border-color: #4a90d9;
  color: #fff;
}

.preset-btn.apply:hover:not(:disabled) {
  background: #5a9fea;
}

.preset-btn.save {
  flex: 1;
  border-color: #4caf50;
  color: #4caf50;
}

.preset-btn.save:hover {
  background: #4caf50;
  color: #fff;
}

.preset-btn.delete {
  border-color: #c44;
  color: #c44;
}

.preset-btn.delete:hover:not(:disabled) {
  background: #c44;
  color: #fff;
}

/* Preset Dialog */
.preset-dialog-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 10000;
}

.preset-dialog {
  background: #2d2d2d;
  border-radius: 8px;
  padding: 20px;
  min-width: 320px;
  box-shadow: 0 8px 32px rgba(0, 0, 0, 0.5);
}

.preset-dialog h3 {
  margin: 0 0 16px 0;
  color: #e0e0e0;
  font-size: 16px;
}

.dialog-field {
  margin-bottom: 12px;
}

.dialog-field label {
  display: block;
  margin-bottom: 4px;
  color: #888;
  font-size: 12px;
}

.dialog-field input {
  width: 100%;
  padding: 8px 10px;
  background: #1e1e1e;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  color: #e0e0e0;
  font-size: 13px;
}

.dialog-field input:focus {
  outline: none;
  border-color: #4a90d9;
}

.dialog-actions {
  display: flex;
  gap: 8px;
  margin-top: 20px;
  justify-content: flex-end;
}

.dialog-btn {
  padding: 8px 16px;
  border: 1px solid #3d3d3d;
  border-radius: 4px;
  font-size: 13px;
  cursor: pointer;
  transition: all 0.15s;
}

.dialog-btn.cancel {
  background: transparent;
  color: #888;
}

.dialog-btn.cancel:hover {
  background: #3d3d3d;
  color: #e0e0e0;
}

.dialog-btn.save {
  background: #4caf50;
  border-color: #4caf50;
  color: #fff;
}

.dialog-btn.save:hover:not(:disabled) {
  background: #5cbf60;
}

.dialog-btn.save:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

/* GPU Acceleration Toggle */
.gpu-row label {
  display: flex;
  align-items: center;
  gap: 6px;
  flex-wrap: wrap;
}

.gpu-status {
  font-size: 11px;
  padding: 2px 6px;
  border-radius: 3px;
  font-weight: 500;
}

.gpu-status.available {
  background: rgba(76, 175, 80, 0.2);
  color: #4caf50;
}

.gpu-status.unavailable {
  background: rgba(136, 136, 136, 0.2);
  color: #888;
}

/* Bake & Export Section */
.bake-info {
  margin-bottom: 12px;
}

.help-text {
  font-size: 11px;
  color: #888;
  margin: 0;
  line-height: 1.4;
}

.bake-actions {
  display: flex;
  gap: 8px;
  margin-top: 12px;
}

.bake-btn {
  flex: 1;
  display: flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  padding: 8px 12px;
  border: 1px solid #444;
  border-radius: 4px;
  background: #333;
  color: #ccc;
  font-size: 12px;
  cursor: pointer;
  transition: all 0.15s;
}

.bake-btn:hover:not(:disabled) {
  background: #3a3a3a;
  border-color: #555;
}

.bake-btn.primary {
  background: #2d5a8a;
  border-color: #3d7ab8;
  color: #fff;
}

.bake-btn.primary:hover:not(:disabled) {
  background: #3d7ab8;
}

.bake-btn:disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.bake-progress {
  margin-top: 12px;
}

.progress-bar {
  height: 6px;
  background: #333;
  border-radius: 3px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: linear-gradient(90deg, #4a90d9, #6ab0ff);
  transition: width 0.2s;
}

.progress-text {
  display: block;
  margin-top: 4px;
  font-size: 11px;
  color: #888;
  text-align: center;
}

.bake-result {
  display: flex;
  align-items: center;
  gap: 8px;
  margin-top: 12px;
  padding: 8px;
  background: rgba(76, 175, 80, 0.1);
  border: 1px solid rgba(76, 175, 80, 0.3);
  border-radius: 4px;
  color: #4caf50;
  font-size: 11px;
}

.bake-result i {
  font-size: 14px;
}
</style>
