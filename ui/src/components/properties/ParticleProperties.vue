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
            <div v-if="emitter.shape !== 'point' && emitter.shape !== 'spline'" class="property-row checkbox-row">
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
    <div class="property-section">
      <div class="section-header" @click="toggleSection('forces')">
        <i class="pi" :class="expandedSections.has('forces') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Force Fields</span>
      </div>
      <div v-if="expandedSections.has('forces')" class="section-content">
        <!-- Tabs -->
        <div class="force-tabs">
          <button
            :class="{ active: forceTab === 'wells' }"
            @click="forceTab = 'wells'"
          >
            Gravity Wells
          </button>
          <button
            :class="{ active: forceTab === 'vortices' }"
            @click="forceTab = 'vortices'"
          >
            Vortices
          </button>
        </div>

        <!-- Gravity Wells -->
        <div v-if="forceTab === 'wells'" class="force-list">
          <button class="add-btn full-width" @click="addGravityWell">
            <i class="pi pi-plus" /> Add Gravity Well
          </button>
          <div
            v-for="well in gravityWells"
            :key="well.id"
            class="force-item"
          >
            <div class="force-header">
              <input
                type="text"
                :value="well.name"
                @input="updateGravityWell(well.id, 'name', ($event.target as HTMLInputElement).value)"
                class="force-name"
              />
              <label class="enabled-toggle">
                <input
                  type="checkbox"
                  :checked="well.enabled"
                  @change="updateGravityWell(well.id, 'enabled', ($event.target as HTMLInputElement).checked)"
                />
              </label>
              <button class="remove-btn" @click="removeGravityWell(well.id)">
                <i class="pi pi-trash" />
              </button>
            </div>
            <div class="property-row">
              <label title="Horizontal position of the gravity well. 0 = left edge, 0.5 = center, 1 = right edge.">Position X</label>
              <input
                type="range"
                :value="well.x"
                min="0"
                max="1"
                step="0.01"
                @input="updateGravityWell(well.id, 'x', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ well.x.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Vertical position of the gravity well. 0 = top edge, 0.5 = center, 1 = bottom edge.">Position Y</label>
              <input
                type="range"
                :value="well.y"
                min="0"
                max="1"
                step="0.01"
                @input="updateGravityWell(well.id, 'y', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ well.y.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Attraction force strength. Positive = attract particles toward center, negative = repel particles away.">Strength</label>
              <input
                type="range"
                :value="well.strength"
                min="-1000"
                max="1000"
                step="10"
                @input="updateGravityWell(well.id, 'strength', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ well.strength }}</span>
            </div>
            <div class="property-row">
              <label title="Area of influence as a fraction of composition size. Particles outside this radius are unaffected.">Radius</label>
              <input
                type="range"
                :value="well.radius"
                min="0.01"
                max="1"
                step="0.01"
                @input="updateGravityWell(well.id, 'radius', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ well.radius.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="How force decreases with distance. Linear = gradual, Quadratic = realistic physics, Constant = uniform force.">Falloff</label>
              <select
                :value="well.falloff"
                @change="updateGravityWell(well.id, 'falloff', ($event.target as HTMLSelectElement).value)"
              >
                <option value="linear">Linear</option>
                <option value="quadratic">Quadratic</option>
                <option value="constant">Constant</option>
              </select>
            </div>
          </div>
        </div>

        <!-- Vortices -->
        <div v-if="forceTab === 'vortices'" class="force-list">
          <button class="add-btn full-width" @click="addVortex">
            <i class="pi pi-plus" /> Add Vortex
          </button>
          <div
            v-for="vortex in vortices"
            :key="vortex.id"
            class="force-item"
          >
            <div class="force-header">
              <input
                type="text"
                :value="vortex.name"
                @input="updateVortex(vortex.id, 'name', ($event.target as HTMLInputElement).value)"
                class="force-name"
              />
              <label class="enabled-toggle">
                <input
                  type="checkbox"
                  :checked="vortex.enabled"
                  @change="updateVortex(vortex.id, 'enabled', ($event.target as HTMLInputElement).checked)"
                />
              </label>
              <button class="remove-btn" @click="removeVortex(vortex.id)">
                <i class="pi pi-trash" />
              </button>
            </div>
            <div class="property-row">
              <label title="Horizontal position of the vortex center. 0 = left edge, 0.5 = center, 1 = right edge.">Position X</label>
              <input
                type="range"
                :value="vortex.x"
                min="0"
                max="1"
                step="0.01"
                @input="updateVortex(vortex.id, 'x', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ vortex.x.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Vertical position of the vortex center. 0 = top edge, 0.5 = center, 1 = bottom edge.">Position Y</label>
              <input
                type="range"
                :value="vortex.y"
                min="0"
                max="1"
                step="0.01"
                @input="updateVortex(vortex.id, 'y', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ vortex.y.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Overall strength of the vortex force applied to particles.">Strength</label>
              <input
                type="range"
                :value="vortex.strength"
                min="0"
                max="1000"
                step="10"
                @input="updateVortex(vortex.id, 'strength', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ vortex.strength }}</span>
            </div>
            <div class="property-row">
              <label title="Area of influence as a fraction of composition size. Particles outside this radius are unaffected.">Radius</label>
              <input
                type="range"
                :value="vortex.radius"
                min="0.01"
                max="1"
                step="0.01"
                @input="updateVortex(vortex.id, 'radius', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ vortex.radius.toFixed(2) }}</span>
            </div>
            <div class="property-row">
              <label title="Angular velocity of the swirl in degrees per frame. Higher values create faster spinning.">Rotation Speed</label>
              <input
                type="range"
                :value="vortex.rotationSpeed"
                min="0"
                max="50"
                step="1"
                @input="updateVortex(vortex.id, 'rotationSpeed', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ vortex.rotationSpeed }}°/f</span>
            </div>
            <div class="property-row">
              <label title="Force pulling particles toward the vortex center. Creates a spiral effect when combined with rotation.">Inward Pull</label>
              <input
                type="range"
                :value="vortex.inwardPull"
                min="0"
                max="100"
                step="1"
                @input="updateVortex(vortex.id, 'inwardPull', Number(($event.target as HTMLInputElement).value))"
              />
              <span class="value-display">{{ vortex.inwardPull }}</span>
            </div>
          </div>
        </div>
      </div>
    </div>

    <!-- Turbulence Fields -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('turbulence')">
        <i class="pi" :class="expandedSections.has('turbulence') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Turbulence</span>
        <button class="add-btn" @click.stop="addTurbulence" title="Add Turbulence Field">
          <i class="pi pi-plus" />
        </button>
      </div>
      <div v-if="expandedSections.has('turbulence')" class="section-content">
        <div
          v-for="turb in turbulenceFields"
          :key="turb.id"
          class="force-item"
        >
          <div class="force-header">
            <span class="force-label">Turbulence Field</span>
            <label class="enabled-toggle">
              <input
                type="checkbox"
                :checked="turb.enabled"
                @change="updateTurbulence(turb.id, 'enabled', ($event.target as HTMLInputElement).checked)"
              />
            </label>
            <button class="remove-btn" @click="removeTurbulence(turb.id)">
              <i class="pi pi-trash" />
            </button>
          </div>
          <div class="property-row">
            <label title="Size of the noise pattern. Smaller values = fine, detailed turbulence. Larger values = broad, sweeping motion.">Scale</label>
            <input
              type="range"
              :value="turb.scale"
              min="0.001"
              max="0.02"
              step="0.001"
              @input="updateTurbulence(turb.id, 'scale', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ turb.scale.toFixed(3) }}</span>
          </div>
          <div class="property-row">
            <label title="How strongly turbulence affects particle movement. Higher values create more chaotic motion.">Strength</label>
            <input
              type="range"
              :value="turb.strength"
              min="0"
              max="500"
              step="10"
              @input="updateTurbulence(turb.id, 'strength', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ turb.strength }}</span>
          </div>
          <div class="property-row">
            <label title="How fast the turbulence pattern changes over time. 0 = static noise, higher = animated turbulence.">Evolution</label>
            <input
              type="range"
              :value="turb.evolutionSpeed"
              min="0"
              max="1"
              step="0.01"
              @input="updateTurbulence(turb.id, 'evolutionSpeed', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ turb.evolutionSpeed.toFixed(2) }}</span>
          </div>
        </div>

        <div v-if="turbulenceFields.length === 0" class="empty-message">
          No turbulence fields. Add one for organic particle motion.
        </div>
      </div>
    </div>

    <!-- Sub-Emitters -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('subEmitters')">
        <i class="pi" :class="expandedSections.has('subEmitters') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Sub-Emitters</span>
        <button class="add-btn" @click.stop="addSubEmitter" title="Add Sub-Emitter">
          <i class="pi pi-plus" />
        </button>
      </div>
      <div v-if="expandedSections.has('subEmitters')" class="section-content">
        <div
          v-for="sub in subEmitters"
          :key="sub.id"
          class="force-item"
        >
          <div class="force-header">
            <select
              :value="sub.parentEmitterId"
              @change="updateSubEmitter(sub.id, 'parentEmitterId', ($event.target as HTMLSelectElement).value)"
              class="sub-emitter-parent"
            >
              <option value="*">All Emitters</option>
              <option v-for="e in emitters" :key="e.id" :value="e.id">{{ e.name }}</option>
            </select>
            <label class="enabled-toggle">
              <input
                type="checkbox"
                :checked="sub.enabled"
                @change="updateSubEmitter(sub.id, 'enabled', ($event.target as HTMLInputElement).checked)"
              />
            </label>
            <button class="remove-btn" @click="removeSubEmitter(sub.id)">
              <i class="pi pi-trash" />
            </button>
          </div>
          <div class="property-row">
            <label title="Event that triggers sub-particle emission. 'On Death' spawns particles when parent particles expire.">Trigger</label>
            <select
              :value="sub.trigger"
              @change="updateSubEmitter(sub.id, 'trigger', ($event.target as HTMLSelectElement).value)"
            >
              <option value="death">On Death</option>
            </select>
          </div>
          <div class="property-row">
            <label title="Number of sub-particles spawned when the trigger event occurs.">Spawn Count</label>
            <input
              type="range"
              :value="sub.spawnCount"
              min="1"
              max="10"
              step="1"
              @input="updateSubEmitter(sub.id, 'spawnCount', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ sub.spawnCount }}</span>
          </div>
          <div class="property-row">
            <label title="How much of the parent particle's velocity is passed to sub-particles. 0% = independent, 100% = same direction.">Inherit Velocity</label>
            <input
              type="range"
              :value="sub.inheritVelocity"
              min="0"
              max="1"
              step="0.1"
              @input="updateSubEmitter(sub.id, 'inheritVelocity', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ (sub.inheritVelocity * 100).toFixed(0) }}%</span>
          </div>
          <div class="property-row">
            <label title="Diameter of sub-particles in pixels. Often smaller than parent particles for sparks/debris effects.">Size</label>
            <input
              type="range"
              :value="sub.size"
              min="1"
              max="100"
              step="1"
              @input="updateSubEmitter(sub.id, 'size', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ sub.size }}px</span>
          </div>
          <div class="property-row">
            <label title="How long sub-particles live in frames. Usually shorter than parent particles.">Lifetime</label>
            <input
              type="range"
              :value="sub.lifetime"
              min="1"
              max="120"
              step="1"
              @input="updateSubEmitter(sub.id, 'lifetime', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ sub.lifetime }}f</span>
          </div>
          <div class="property-row">
            <label title="Initial velocity of sub-particles in pixels per second.">Speed</label>
            <input
              type="range"
              :value="sub.speed"
              min="1"
              max="500"
              step="10"
              @input="updateSubEmitter(sub.id, 'speed', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ sub.speed }}</span>
          </div>
          <div class="property-row">
            <label title="Angular spread of sub-particle emission. 360° = emit in all directions (explosion), 0° = emit in inherited direction.">Spread</label>
            <input
              type="range"
              :value="sub.spread"
              min="0"
              max="360"
              step="5"
              @input="updateSubEmitter(sub.id, 'spread', Number(($event.target as HTMLInputElement).value))"
            />
            <span class="value-display">{{ sub.spread }}°</span>
          </div>
          <div class="property-row">
            <label title="Color of sub-particles. Can differ from parent for visual variety.">Color</label>
            <input
              type="color"
              :value="rgbToHex(sub.color)"
              @input="updateSubEmitterColor(sub.id, ($event.target as HTMLInputElement).value)"
            />
          </div>
        </div>

        <div v-if="subEmitters.length === 0" class="empty-message">
          No sub-emitters. Add one for particle death effects.
        </div>
      </div>
    </div>

    <!-- Modulations -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('modulations')">
        <i class="pi" :class="expandedSections.has('modulations') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Modulations</span>
        <button class="add-btn" @click.stop="addModulation" title="Add Modulation">
          <i class="pi pi-plus" />
        </button>
      </div>
      <div v-if="expandedSections.has('modulations')" class="section-content">
        <div
          v-for="mod in modulations"
          :key="mod.id"
          class="modulation-item"
        >
          <div class="modulation-header">
            <select
              :value="mod.emitterId"
              @change="updateModulation(mod.id, 'emitterId', ($event.target as HTMLSelectElement).value)"
            >
              <option value="*">All Emitters</option>
              <option v-for="e in emitters" :key="e.id" :value="e.id">{{ e.name }}</option>
            </select>
            <button class="remove-btn" @click="removeModulation(mod.id)">
              <i class="pi pi-trash" />
            </button>
          </div>
          <div class="property-row">
            <label title="Which particle property to animate over the particle's lifetime.">Property</label>
            <select
              :value="mod.property"
              @change="updateModulation(mod.id, 'property', ($event.target as HTMLSelectElement).value)"
            >
              <option value="size">Size</option>
              <option value="speed">Speed</option>
              <option value="opacity">Opacity</option>
              <option value="colorR">Color R</option>
              <option value="colorG">Color G</option>
              <option value="colorB">Color B</option>
            </select>
          </div>
          <div class="property-row">
            <label title="Value of the property when the particle is born.">Start Value</label>
            <input
              type="number"
              :value="mod.startValue"
              step="0.1"
              @input="updateModulation(mod.id, 'startValue', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label title="Value of the property when the particle dies.">End Value</label>
            <input
              type="number"
              :value="mod.endValue"
              step="0.1"
              @input="updateModulation(mod.id, 'endValue', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label title="Interpolation curve between start and end values. Linear = constant rate, Ease Out = fast then slow.">Easing</label>
            <select
              :value="mod.easing"
              @change="updateModulation(mod.id, 'easing', ($event.target as HTMLSelectElement).value)"
            >
              <option value="linear">Linear</option>
              <option value="easeIn">Ease In</option>
              <option value="easeOut">Ease Out</option>
              <option value="easeInOut">Ease In Out</option>
              <option value="bounce">Bounce</option>
              <option value="elastic">Elastic</option>
            </select>
          </div>
        </div>

        <div v-if="modulations.length === 0" class="empty-message">
          No modulations. Add one to animate particle properties over lifetime.
        </div>
      </div>
    </div>

    <!-- Render Options -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('render')">
        <i class="pi" :class="expandedSections.has('render') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>Render Options</span>
      </div>
      <div v-if="expandedSections.has('render')" class="section-content">
        <div class="property-row">
          <label title="How particles blend with the background. Additive = bright/glowing, Multiply = darken, Screen = lighten.">Blend Mode</label>
          <select
            :value="renderOptions.blendMode"
            @change="updateRenderOption('blendMode', ($event.target as HTMLSelectElement).value)"
          >
            <option value="normal">Normal</option>
            <option value="additive">Additive</option>
            <option value="multiply">Multiply</option>
            <option value="screen">Screen</option>
          </select>
        </div>
        <div class="property-row">
          <label title="Visual shape used to render each particle.">Shape</label>
          <select
            :value="renderOptions.particleShape"
            @change="updateRenderOption('particleShape', ($event.target as HTMLSelectElement).value)"
          >
            <option value="circle">Circle</option>
            <option value="square">Square</option>
            <option value="triangle">Triangle</option>
            <option value="star">Star</option>
          </select>
        </div>

        <!-- Sprite Sheet Settings -->
        <div class="property-row checkbox-row">
          <label title="Use a custom image or sprite sheet instead of procedural shapes.">
            <input
              type="checkbox"
              :checked="renderOptions.spriteEnabled"
              @change="updateRenderOption('spriteEnabled', ($event.target as HTMLInputElement).checked)"
            />
            Use Sprite
          </label>
        </div>
        <div v-if="renderOptions.spriteEnabled" class="property-row">
          <label title="URL or data URI of the sprite image.">Sprite URL</label>
          <input
            type="text"
            :value="renderOptions.spriteImageUrl"
            placeholder="https://... or data:..."
            @change="updateRenderOption('spriteImageUrl', ($event.target as HTMLInputElement).value)"
          />
        </div>
        <div v-if="renderOptions.spriteEnabled" class="property-row">
          <label title="Number of columns in the sprite sheet (1 for single image).">Columns</label>
          <input
            type="number"
            :value="renderOptions.spriteColumns"
            min="1"
            max="16"
            @change="updateRenderOption('spriteColumns', Number(($event.target as HTMLInputElement).value))"
          />
        </div>
        <div v-if="renderOptions.spriteEnabled" class="property-row">
          <label title="Number of rows in the sprite sheet (1 for single image).">Rows</label>
          <input
            type="number"
            :value="renderOptions.spriteRows"
            min="1"
            max="16"
            @change="updateRenderOption('spriteRows', Number(($event.target as HTMLInputElement).value))"
          />
        </div>
        <div v-if="renderOptions.spriteEnabled && (renderOptions.spriteColumns > 1 || renderOptions.spriteRows > 1)" class="property-row checkbox-row">
          <label title="Animate through sprite sheet frames over time.">
            <input
              type="checkbox"
              :checked="renderOptions.spriteAnimate"
              @change="updateRenderOption('spriteAnimate', ($event.target as HTMLInputElement).checked)"
            />
            Animate Frames
          </label>
        </div>
        <div v-if="renderOptions.spriteEnabled && renderOptions.spriteAnimate" class="property-row">
          <label title="Frames per second for sprite animation.">Frame Rate</label>
          <input
            type="range"
            :value="renderOptions.spriteFrameRate"
            min="1"
            max="60"
            step="1"
            @input="updateRenderOption('spriteFrameRate', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.spriteFrameRate }} fps</span>
        </div>
        <div v-if="renderOptions.spriteEnabled && (renderOptions.spriteColumns > 1 || renderOptions.spriteRows > 1)" class="property-row checkbox-row">
          <label title="Each particle starts at a random frame in the sprite sheet.">
            <input
              type="checkbox"
              :checked="renderOptions.spriteRandomStart"
              @change="updateRenderOption('spriteRandomStart', ($event.target as HTMLInputElement).checked)"
            />
            Random Start Frame
          </label>
        </div>

        <div class="property-row checkbox-row">
          <label title="Draw a trail behind moving particles showing their recent path.">
            <input
              type="checkbox"
              :checked="renderOptions.renderTrails"
              @change="updateRenderOption('renderTrails', ($event.target as HTMLInputElement).checked)"
            />
            Render Trails
          </label>
        </div>
        <div v-if="renderOptions.renderTrails" class="property-row">
          <label title="Number of historical positions to show in the trail.">Trail Length</label>
          <input
            type="range"
            :value="renderOptions.trailLength"
            min="1"
            max="20"
            step="1"
            @input="updateRenderOption('trailLength', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.trailLength }}</span>
        </div>
        <div v-if="renderOptions.renderTrails" class="property-row">
          <label title="How quickly trail opacity decreases. Higher values = faster fade.">Trail Falloff</label>
          <input
            type="range"
            :value="renderOptions.trailOpacityFalloff"
            min="0"
            max="1"
            step="0.05"
            @input="updateRenderOption('trailOpacityFalloff', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.trailOpacityFalloff.toFixed(2) }}</span>
        </div>
        <div class="property-row checkbox-row">
          <label title="Add a soft glow effect around particles. Great for fire, magic, and light effects.">
            <input
              type="checkbox"
              :checked="renderOptions.glowEnabled"
              @change="updateRenderOption('glowEnabled', ($event.target as HTMLInputElement).checked)"
            />
            Enable Glow
          </label>
        </div>
        <div v-if="renderOptions.glowEnabled" class="property-row">
          <label title="Size of the glow area around each particle.">Glow Radius</label>
          <input
            type="range"
            :value="renderOptions.glowRadius"
            min="1"
            max="50"
            step="1"
            @input="updateRenderOption('glowRadius', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.glowRadius }}px</span>
        </div>
        <div v-if="renderOptions.glowEnabled" class="property-row">
          <label title="Brightness of the glow effect. 0 = no glow, 1 = maximum glow.">Glow Intensity</label>
          <input
            type="range"
            :value="renderOptions.glowIntensity"
            min="0"
            max="1"
            step="0.05"
            @input="updateRenderOption('glowIntensity', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.glowIntensity.toFixed(2) }}</span>
        </div>

        <!-- Motion Blur -->
        <div class="subsection-divider">Motion Blur</div>
        <div class="property-row checkbox-row">
          <label title="Blur fast-moving particles to simulate camera motion blur.">
            <input
              type="checkbox"
              :checked="renderOptions.motionBlur"
              @change="updateRenderOption('motionBlur', ($event.target as HTMLInputElement).checked)"
            />
            Enable Motion Blur
          </label>
        </div>
        <div v-if="renderOptions.motionBlur" class="property-row">
          <label title="How much blur to apply based on particle velocity.">Blur Strength</label>
          <input
            type="range"
            :value="renderOptions.motionBlurStrength"
            min="0"
            max="1"
            step="0.05"
            @input="updateRenderOption('motionBlurStrength', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.motionBlurStrength.toFixed(2) }}</span>
        </div>
        <div v-if="renderOptions.motionBlur" class="property-row">
          <label title="Number of samples for blur quality. Higher = smoother but slower.">Blur Samples</label>
          <input
            type="range"
            :value="renderOptions.motionBlurSamples"
            min="1"
            max="16"
            step="1"
            @input="updateRenderOption('motionBlurSamples', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ renderOptions.motionBlurSamples }}</span>
        </div>

        <!-- Particle Connections -->
        <div class="subsection-divider">Particle Connections</div>
        <div class="property-row checkbox-row">
          <label title="Draw lines between nearby particles. Creates web/network/constellation effects.">
            <input
              type="checkbox"
              :checked="connections.enabled"
              @change="updateConnection('enabled', ($event.target as HTMLInputElement).checked)"
            />
            Enable Connections
          </label>
        </div>
        <div v-if="connections.enabled" class="property-row">
          <label title="Maximum distance in pixels between particles to draw a connection.">Max Distance</label>
          <input
            type="range"
            :value="connections.maxDistance"
            min="10"
            max="300"
            step="10"
            @input="updateConnection('maxDistance', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ connections.maxDistance }}px</span>
        </div>
        <div v-if="connections.enabled" class="property-row">
          <label title="Maximum number of connections each particle can have.">Max Connections</label>
          <input
            type="range"
            :value="connections.maxConnections"
            min="1"
            max="5"
            step="1"
            @input="updateConnection('maxConnections', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ connections.maxConnections }}</span>
        </div>
        <div v-if="connections.enabled" class="property-row">
          <label title="Thickness of connection lines in pixels.">Line Width</label>
          <input
            type="range"
            :value="connections.lineWidth"
            min="0.5"
            max="3"
            step="0.1"
            @input="updateConnection('lineWidth', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ connections.lineWidth.toFixed(1) }}</span>
        </div>
        <div v-if="connections.enabled" class="property-row">
          <label title="Transparency of connection lines. 0 = invisible, 1 = fully opaque.">Line Opacity</label>
          <input
            type="range"
            :value="connections.lineOpacity"
            min="0"
            max="1"
            step="0.05"
            @input="updateConnection('lineOpacity', Number(($event.target as HTMLInputElement).value))"
          />
          <span class="value-display">{{ connections.lineOpacity.toFixed(2) }}</span>
        </div>
        <div v-if="connections.enabled" class="property-row checkbox-row">
          <label title="Make connection lines more transparent as particles get farther apart.">
            <input
              type="checkbox"
              :checked="connections.fadeByDistance"
              @change="updateConnection('fadeByDistance', ($event.target as HTMLInputElement).checked)"
            />
            Fade by Distance
          </label>
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
import { ref, computed, onMounted, watch } from 'vue';
import type {
  Layer,
  ParticleLayerData,
  ParticleSystemLayerConfig,
  ParticleEmitterConfig,
  GravityWellConfig,
  VortexConfig,
  ParticleModulationConfig,
  ParticleRenderOptions,
  TurbulenceFieldConfig,
  SubEmitterConfig,
  ConnectionRenderConfig
} from '@/types/project';
import { usePresetStore } from '@/stores/presetStore';
import type { ParticlePreset } from '@/types/presets';
import { ParticleGPUCompute } from '@/services/particleGPU';

// Preset Store
const presetStore = usePresetStore();
presetStore.initialize();

// WebGPU Detection
const webgpuAvailable = ref(false);

onMounted(async () => {
  webgpuAvailable.value = await ParticleGPUCompute.isAvailable();
});

// Preset UI State
const selectedPresetId = ref('');
const showSaveDialog = ref(false);
const newPresetName = ref('');
const newPresetDescription = ref('');
const newPresetTags = ref('');

// Computed preset lists
const builtInPresets = computed(() =>
  presetStore.particlePresets.filter(p => p.isBuiltIn)
);
const userPresets = computed(() =>
  presetStore.particlePresets.filter(p => !p.isBuiltIn)
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
  particleCount: 0
});

const emit = defineEmits<{
  (e: 'update', data: Partial<ParticleLayerData>): void;
}>();

// UI State - persist expanded sections per layer
const expandedSectionsMap = ref<Map<string, Set<string>>>(new Map());
const expandedEmittersMap = ref<Map<string, Set<string>>>(new Map());
const forceTab = ref<'wells' | 'vortices'>('wells');

// Get/set expanded sections for current layer
const expandedSections = computed({
  get: () => {
    const layerId = props.layer?.id;
    if (!layerId) return new Set(['system', 'emitters']);
    if (!expandedSectionsMap.value.has(layerId)) {
      expandedSectionsMap.value.set(layerId, new Set(['system', 'emitters']));
    }
    return expandedSectionsMap.value.get(layerId)!;
  },
  set: (val: Set<string>) => {
    const layerId = props.layer?.id;
    if (layerId) {
      expandedSectionsMap.value.set(layerId, val);
    }
  }
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
  }
});

// Watch for layer changes to ensure UI stays in sync
watch(() => props.layer?.id, (newId, oldId) => {
  if (newId && newId !== oldId) {
    // Initialize expanded sections for new layer if not already set
    if (!expandedSectionsMap.value.has(newId)) {
      expandedSectionsMap.value.set(newId, new Set(['system', 'emitters']));
    }
    if (!expandedEmittersMap.value.has(newId)) {
      expandedEmittersMap.value.set(newId, new Set<string>());
    }
  }
}, { immediate: true });

// Deep watch for layer data changes to ensure computed properties update
watch(() => props.layer?.data, () => {
  // Force re-evaluation of computed properties when layer data changes externally
}, { deep: true });

// Get layer data with defaults
const layerData = computed((): ParticleLayerData => {
  const data = props.layer.data as ParticleLayerData | null;
  return data || {
    systemConfig: {
      maxParticles: 10000,
      gravity: 0,
      windStrength: 0,
      windDirection: 0,
      warmupPeriod: 0,
      respectMaskBoundary: false,
      boundaryBehavior: 'kill',
      friction: 0.01
    },
    emitters: [],
    gravityWells: [],
    vortices: [],
    modulations: [],
    renderOptions: {
      blendMode: 'additive',
      renderTrails: false,
      trailLength: 5,
      trailOpacityFalloff: 0.7,
      particleShape: 'circle',
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
        fadeByDistance: true
      },
      // Sprite defaults
      spriteEnabled: false,
      spriteImageUrl: '',
      spriteColumns: 1,
      spriteRows: 1,
      spriteAnimate: false,
      spriteFrameRate: 10,
      spriteRandomStart: false
    },
    turbulenceFields: [],
    subEmitters: []
  };
});

const systemConfig = computed(() => layerData.value.systemConfig);
const emitters = computed(() => layerData.value.emitters);
const gravityWells = computed(() => layerData.value.gravityWells);
const vortices = computed(() => layerData.value.vortices);
const modulations = computed(() => layerData.value.modulations);
const renderOptions = computed(() => layerData.value.renderOptions);
const turbulenceFields = computed(() => layerData.value.turbulenceFields || []);
const subEmitters = computed(() => layerData.value.subEmitters || []);
const connections = computed(() => renderOptions.value.connections || {
  enabled: false,
  maxDistance: 100,
  maxConnections: 3,
  lineWidth: 1,
  lineOpacity: 0.5,
  fadeByDistance: true
});
const particleCount = computed(() => props.particleCount);

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

  const preset = presetStore.getPreset(selectedPresetId.value) as ParticlePreset | undefined;
  if (!preset || preset.category !== 'particle') return;

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
  if (config.gravity) {
    updates.systemConfig = {
      ...(updates.systemConfig || systemConfig.value),
      gravity: config.gravity.y || 0,
    };
  }

  // Apply emitter defaults if specified
  if (config.emissionRate || config.lifespan || config.startSize || config.endSize) {
    const defaultEmitter = emitters.value[0] || createDefaultEmitter();
    updates.emitters = [{
      ...defaultEmitter,
      emissionRate: config.emissionRate ?? defaultEmitter.emissionRate,
      lifespan: config.lifespan ?? defaultEmitter.lifespan,
      startSize: config.startSize ?? defaultEmitter.startSize,
      endSize: config.endSize ?? defaultEmitter.endSize,
      startColor: config.startColor ?? defaultEmitter.startColor,
      endColor: config.endColor ?? defaultEmitter.endColor,
      velocitySpread: config.velocitySpread ?? defaultEmitter.velocitySpread,
    }];
  }

  // Apply turbulence if specified
  if (config.turbulenceStrength !== undefined) {
    updates.turbulenceFields = [{
      id: 'turbulence-from-preset',
      enabled: true,
      strength: config.turbulenceStrength,
      scale: 0.01,
      octaves: 3,
      persistence: 0.5,
      animationSpeed: 1,
    }];
  }

  emit('update', updates);
}

function createDefaultEmitter(): ParticleEmitterConfig {
  return {
    id: `emitter_${Date.now()}`,
    enabled: true,
    emissionMode: 'point',
    emissionRate: 50,
    emissionBurstSize: 10,
    emissionBurstInterval: 0,
    position: { x: 0, y: 0, z: 0 },
    direction: { x: 0, y: -1, z: 0 },
    spread: 30,
    velocity: { min: 50, max: 150 },
    lifespan: 2,
    startSize: 10,
    endSize: 2,
    startColor: '#ffffff',
    endColor: '#ffffff',
    startOpacity: 1,
    endOpacity: 0,
    rotation: { min: 0, max: 360 },
    rotationSpeed: { min: 0, max: 0 },
    velocitySpread: 30,
  };
}

function saveCurrentAsPreset(): void {
  if (!newPresetName.value.trim()) return;

  const tags = newPresetTags.value
    .split(',')
    .map(t => t.trim())
    .filter(t => t.length > 0);

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
      gravity: { x: 0, y: systemConfig.value.gravity, z: 0 },
      turbulenceStrength: turbulence?.strength,
      velocitySpread: emitter?.velocitySpread,
    },
    {
      description: newPresetDescription.value.trim() || undefined,
      tags: tags.length > 0 ? tags : undefined,
    }
  );

  // Reset dialog
  showSaveDialog.value = false;
  newPresetName.value = '';
  newPresetDescription.value = '';
  newPresetTags.value = '';
}

function deleteSelectedPreset(): void {
  if (!selectedPresetId.value || isBuiltInPreset.value) return;

  if (confirm('Delete this preset?')) {
    presetStore.deletePreset(selectedPresetId.value);
    selectedPresetId.value = '';
  }
}

// Update functions
function updateSystemConfig(key: keyof ParticleSystemLayerConfig, value: any): void {
  emit('update', {
    systemConfig: { ...systemConfig.value, [key]: value }
  });
}

function updateEmitter(id: string, key: keyof ParticleEmitterConfig, value: any): void {
  const updated = emitters.value.map(e =>
    e.id === id ? { ...e, [key]: value } : e
  );
  emit('update', { emitters: updated });
}

function updateEmitterColor(id: string, hex: string): void {
  const rgb = hexToRgb(hex);
  updateEmitter(id, 'color', rgb);
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
    burstCount: 20
  };
  emit('update', { emitters: [...emitters.value, newEmitter] });
  expandedEmitters.value.add(newEmitter.id);
}

function removeEmitter(id: string): void {
  emit('update', { emitters: emitters.value.filter(e => e.id !== id) });
}

function updateGravityWell(id: string, key: keyof GravityWellConfig, value: any): void {
  const updated = gravityWells.value.map(w =>
    w.id === id ? { ...w, [key]: value } : w
  );
  emit('update', { gravityWells: updated });
}

function addGravityWell(): void {
  const newWell: GravityWellConfig = {
    id: `well_${Date.now()}`,
    name: `Gravity Well ${gravityWells.value.length + 1}`,
    x: 0.5,
    y: 0.5,
    strength: 100,
    radius: 0.3,
    falloff: 'quadratic',
    enabled: true
  };
  emit('update', { gravityWells: [...gravityWells.value, newWell] });
}

function removeGravityWell(id: string): void {
  emit('update', { gravityWells: gravityWells.value.filter(w => w.id !== id) });
}

function updateVortex(id: string, key: keyof VortexConfig, value: any): void {
  const updated = vortices.value.map(v =>
    v.id === id ? { ...v, [key]: value } : v
  );
  emit('update', { vortices: updated });
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
    enabled: true
  };
  emit('update', { vortices: [...vortices.value, newVortex] });
}

function removeVortex(id: string): void {
  emit('update', { vortices: vortices.value.filter(v => v.id !== id) });
}

function updateModulation(id: string, key: keyof ParticleModulationConfig, value: any): void {
  const updated = modulations.value.map(m =>
    m.id === id ? { ...m, [key]: value } : m
  );
  emit('update', { modulations: updated });
}

function addModulation(): void {
  const newMod: ParticleModulationConfig = {
    id: `mod_${Date.now()}`,
    emitterId: '*',
    property: 'opacity',
    startValue: 1,
    endValue: 0,
    easing: 'linear'
  };
  emit('update', { modulations: [...modulations.value, newMod] });
}

function removeModulation(id: string): void {
  emit('update', { modulations: modulations.value.filter(m => m.id !== id) });
}

function updateRenderOption(key: keyof ParticleRenderOptions, value: any): void {
  emit('update', {
    renderOptions: { ...renderOptions.value, [key]: value }
  });
}

// Connection functions
function updateConnection(key: keyof ConnectionRenderConfig, value: any): void {
  emit('update', {
    renderOptions: {
      ...renderOptions.value,
      connections: { ...connections.value, [key]: value }
    }
  });
}

// Turbulence functions
function updateTurbulence(id: string, key: keyof TurbulenceFieldConfig, value: any): void {
  const updated = turbulenceFields.value.map(t =>
    t.id === id ? { ...t, [key]: value } : t
  );
  emit('update', { turbulenceFields: updated });
}

function addTurbulence(): void {
  const newTurb: TurbulenceFieldConfig = {
    id: `turb_${Date.now()}`,
    enabled: true,
    scale: 0.005,
    strength: 100,
    evolutionSpeed: 0.1
  };
  emit('update', { turbulenceFields: [...turbulenceFields.value, newTurb] });
}

function removeTurbulence(id: string): void {
  emit('update', { turbulenceFields: turbulenceFields.value.filter(t => t.id !== id) });
}

// Sub-emitter functions
function updateSubEmitter(id: string, key: keyof SubEmitterConfig, value: any): void {
  const updated = subEmitters.value.map(s =>
    s.id === id ? { ...s, [key]: value } : s
  );
  emit('update', { subEmitters: updated });
}

function updateSubEmitterColor(id: string, hex: string): void {
  const rgb = hexToRgb(hex);
  updateSubEmitter(id, 'color', rgb);
}

function addSubEmitter(): void {
  const newSub: SubEmitterConfig = {
    id: `sub_${Date.now()}`,
    parentEmitterId: '*',
    trigger: 'death',
    spawnCount: 3,
    inheritVelocity: 0.5,
    size: 5,
    sizeVariance: 2,
    lifetime: 30,
    speed: 50,
    spread: 360,
    color: [255, 200, 100],
    enabled: true
  };
  emit('update', { subEmitters: [...subEmitters.value, newSub] });
}

function removeSubEmitter(id: string): void {
  emit('update', { subEmitters: subEmitters.value.filter(s => s.id !== id) });
}

// Color utilities
function rgbToHex(rgb: [number, number, number]): string {
  return '#' + rgb.map(c => c.toString(16).padStart(2, '0')).join('');
}

function hexToRgb(hex: string): [number, number, number] {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  return result
    ? [parseInt(result[1], 16), parseInt(result[2], 16), parseInt(result[3], 16)]
    : [255, 255, 255];
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
</style>
