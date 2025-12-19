<template>
  <div class="particle-properties">
    <!-- System Settings -->
    <div class="property-section">
      <div class="section-header" @click="toggleSection('system')">
        <i class="pi" :class="expandedSections.has('system') ? 'pi-chevron-down' : 'pi-chevron-right'" />
        <span>System Settings</span>
      </div>
      <div v-if="expandedSections.has('system')" class="section-content">
        <div class="property-row">
          <label>Max Particles</label>
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
          <label>Gravity</label>
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
          <label>Wind Strength</label>
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
          <label>Wind Direction</label>
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
          <label>Friction</label>
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
          <label>Boundary</label>
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
          <label>Warmup Period</label>
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
          <label>
            <input
              type="checkbox"
              :checked="systemConfig.respectMaskBoundary"
              @change="updateSystemConfig('respectMaskBoundary', ($event.target as HTMLInputElement).checked)"
            />
            Respect Mask Boundary
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
              <label>Position X</label>
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
              <label>Position Y</label>
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
              <label>Direction</label>
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
              <label>Spread</label>
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
              <label>Speed</label>
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
              <label>Speed Variance</label>
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
              <label>Size</label>
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
              <label>Size Variance</label>
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
              <label>Color</label>
              <input
                type="color"
                :value="rgbToHex(emitter.color)"
                @input="updateEmitterColor(emitter.id, ($event.target as HTMLInputElement).value)"
              />
            </div>
            <div class="property-row">
              <label>Emission Rate</label>
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
              <label>Lifetime</label>
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
              <label>Initial Burst</label>
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
              <label>
                <input
                  type="checkbox"
                  :checked="emitter.burstOnBeat"
                  @change="updateEmitter(emitter.id, 'burstOnBeat', ($event.target as HTMLInputElement).checked)"
                />
                Burst on Beat
              </label>
            </div>
            <div v-if="emitter.burstOnBeat" class="property-row">
              <label>Burst Count</label>
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
              <label>Shape</label>
              <select
                :value="emitter.shape || 'point'"
                @change="updateEmitter(emitter.id, 'shape', ($event.target as HTMLSelectElement).value)"
              >
                <option value="point">Point</option>
                <option value="line">Line</option>
                <option value="circle">Circle</option>
                <option value="box">Box</option>
                <option value="sphere">Sphere</option>
                <option value="ring">Ring</option>
                <option value="spline">Spline Path</option>
              </select>
            </div>
            <div v-if="emitter.shape === 'circle' || emitter.shape === 'sphere' || emitter.shape === 'ring'" class="property-row">
              <label>Radius</label>
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
              <label>Inner Radius</label>
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
              <label>Width</label>
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
              <label>Height</label>
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
              <label>Length</label>
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
            <div v-if="emitter.shape !== 'point' && emitter.shape !== 'spline'" class="property-row checkbox-row">
              <label>
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
              <label>Position X</label>
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
              <label>Position Y</label>
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
              <label>Strength</label>
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
              <label>Radius</label>
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
              <label>Falloff</label>
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
              <label>Position X</label>
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
              <label>Position Y</label>
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
              <label>Strength</label>
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
              <label>Radius</label>
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
              <label>Rotation Speed</label>
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
              <label>Inward Pull</label>
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
            <label>Scale</label>
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
            <label>Strength</label>
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
            <label>Evolution</label>
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
            <label>Trigger</label>
            <select
              :value="sub.trigger"
              @change="updateSubEmitter(sub.id, 'trigger', ($event.target as HTMLSelectElement).value)"
            >
              <option value="death">On Death</option>
            </select>
          </div>
          <div class="property-row">
            <label>Spawn Count</label>
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
            <label>Inherit Velocity</label>
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
            <label>Size</label>
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
            <label>Lifetime</label>
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
            <label>Speed</label>
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
            <label>Spread</label>
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
            <label>Color</label>
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
            <label>Property</label>
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
            <label>Start Value</label>
            <input
              type="number"
              :value="mod.startValue"
              step="0.1"
              @input="updateModulation(mod.id, 'startValue', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label>End Value</label>
            <input
              type="number"
              :value="mod.endValue"
              step="0.1"
              @input="updateModulation(mod.id, 'endValue', Number(($event.target as HTMLInputElement).value))"
            />
          </div>
          <div class="property-row">
            <label>Easing</label>
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
          <label>Blend Mode</label>
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
          <label>Shape</label>
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
        <div class="property-row checkbox-row">
          <label>
            <input
              type="checkbox"
              :checked="renderOptions.renderTrails"
              @change="updateRenderOption('renderTrails', ($event.target as HTMLInputElement).checked)"
            />
            Render Trails
          </label>
        </div>
        <div v-if="renderOptions.renderTrails" class="property-row">
          <label>Trail Length</label>
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
          <label>Trail Falloff</label>
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
          <label>
            <input
              type="checkbox"
              :checked="renderOptions.glowEnabled"
              @change="updateRenderOption('glowEnabled', ($event.target as HTMLInputElement).checked)"
            />
            Enable Glow
          </label>
        </div>
        <div v-if="renderOptions.glowEnabled" class="property-row">
          <label>Glow Radius</label>
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
          <label>Glow Intensity</label>
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
          <label>
            <input
              type="checkbox"
              :checked="renderOptions.motionBlur"
              @change="updateRenderOption('motionBlur', ($event.target as HTMLInputElement).checked)"
            />
            Enable Motion Blur
          </label>
        </div>
        <div v-if="renderOptions.motionBlur" class="property-row">
          <label>Blur Strength</label>
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
          <label>Blur Samples</label>
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
          <label>
            <input
              type="checkbox"
              :checked="connections.enabled"
              @change="updateConnection('enabled', ($event.target as HTMLInputElement).checked)"
            />
            Enable Connections
          </label>
        </div>
        <div v-if="connections.enabled" class="property-row">
          <label>Max Distance</label>
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
          <label>Max Connections</label>
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
          <label>Line Width</label>
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
          <label>Line Opacity</label>
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
          <label>
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
import { ref, computed } from 'vue';
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

// UI State
const expandedSections = ref(new Set(['system', 'emitters']));
const expandedEmitters = ref(new Set<string>());
const forceTab = ref<'wells' | 'vortices'>('wells');

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
      }
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

// Section toggle
function toggleSection(section: string): void {
  if (expandedSections.value.has(section)) {
    expandedSections.value.delete(section);
  } else {
    expandedSections.value.add(section);
  }
}

function toggleEmitter(id: string): void {
  if (expandedEmitters.value.has(id)) {
    expandedEmitters.value.delete(id);
  } else {
    expandedEmitters.value.add(id);
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
</style>
