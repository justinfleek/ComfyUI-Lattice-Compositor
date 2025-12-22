<template>
  <div class="text-properties">
    <div class="prop-section">
      <div class="section-title">Source Text</div>
      <textarea
        :value="textData.text"
        @input="e => updateText((e.target as HTMLTextAreaElement).value)"
        class="text-area"
        rows="3"
      ></textarea>
    </div>

    <div class="prop-section">
      <div class="section-title">Character</div>
      <div class="row font-row">
         <select :value="textData.fontFamily" @change="e => handleFontChange((e.target as HTMLSelectElement).value)" class="font-select">
            <template v-for="category in fontCategories" :key="category.name">
              <optgroup :label="category.name">
                <option v-for="font in category.fonts" :key="font.family" :value="font.family">
                  {{ font.family }}
                </option>
              </optgroup>
            </template>
         </select>
         <div class="style-toggles">
            <button :class="{active: textData.fontWeight === 'bold'}" @click="toggleBold">B</button>
            <button :class="{active: textData.fontStyle === 'italic'}" @click="toggleItalic">I</button>
         </div>
      </div>
      <div class="row" v-if="!hasSystemFonts">
         <button class="font-access-btn" @click="requestFontAccess" :disabled="loadingFonts">
           {{ loadingFonts ? 'Loading...' : '+ Load System Fonts' }}
         </button>
      </div>

      <div class="row">
         <label>Size</label>
         <ScrubableNumber :modelValue="getPropertyValue('Font Size') || textData.fontSize" @update:modelValue="v => updateAnimatable('Font Size', v)" />
      </div>

      <div class="row color-row">
         <div class="color-item">
            <input type="color" :value="textData.fill" @input="e => updateData('fill', (e.target as HTMLInputElement).value)" />
            <span>Fill</span>
         </div>
         <div class="color-item">
            <input type="color" :value="textData.stroke || '#000000'" @input="e => updateData('stroke', (e.target as HTMLInputElement).value)" />
            <span>Stroke</span>
         </div>
      </div>

      <div class="row">
         <label>Stroke Width</label>
         <ScrubableNumber :modelValue="getPropertyValue('Stroke Width') || textData.strokeWidth || 0" @update:modelValue="v => updateAnimatable('Stroke Width', v)" :min="0" :max="50" />
      </div>

      <div class="row">
         <label>Alignment</label>
         <div class="align-buttons">
            <button :class="{ active: textData.textAlign === 'left' }" @click="updateData('textAlign', 'left')">◀</button>
            <button :class="{ active: textData.textAlign === 'center' }" @click="updateData('textAlign', 'center')">▬</button>
            <button :class="{ active: textData.textAlign === 'right' }" @click="updateData('textAlign', 'right')">▶</button>
         </div>
      </div>
    </div>

    <div class="prop-section">
      <div class="section-title">Transform</div>

      <div class="row">
         <label>Position</label>
         <div class="vec2">
            <ScrubableNumber :modelValue="transform.position.value.x" @update:modelValue="v => updateTransform('position', 'x', v)" />
            <ScrubableNumber :modelValue="transform.position.value.y" @update:modelValue="v => updateTransform('position', 'y', v)" />
         </div>
      </div>
      <div class="row">
         <label>Origin</label>
         <div class="vec2">
            <ScrubableNumber :modelValue="transform.anchorPoint.value.x" @update:modelValue="v => updateTransform('anchorPoint', 'x', v)" />
            <ScrubableNumber :modelValue="transform.anchorPoint.value.y" @update:modelValue="v => updateTransform('anchorPoint', 'y', v)" />
         </div>
      </div>
      <div class="row">
         <label>Scale %</label>
         <div class="vec2">
            <ScrubableNumber :modelValue="transform.scale.value.x" @update:modelValue="v => updateTransform('scale', 'x', v)" />
            <ScrubableNumber :modelValue="transform.scale.value.y" @update:modelValue="v => updateTransform('scale', 'y', v)" />
         </div>
      </div>
      <div class="row">
         <label>Rotation</label>
         <ScrubableNumber :modelValue="transform.rotation.value" @update:modelValue="v => updateTransform('rotation', null, v)" />
      </div>
      <div class="row">
         <label>Opacity</label>
         <ScrubableNumber :modelValue="layer.opacity?.value ?? 100" @update:modelValue="v => updateOpacity(v)" :min="0" :max="100" />
      </div>
    </div>

    <div class="prop-section">
       <div class="section-title">Path Options</div>
       <div class="row">
          <label>Path</label>
          <select :value="textData.pathLayerId || ''" @change="e => updateData('pathLayerId', (e.target as HTMLSelectElement).value || null)" class="full-select">
             <option value="">None</option>
             <option v-for="l in splineLayers" :key="l.id" :value="l.id">{{ l.type === 'path' ? '⤳ ' : '〰 ' }}{{ l.name }}</option>
          </select>
       </div>

       <template v-if="textData.pathLayerId">
         <div class="row">
            <label>Path Offset %</label>
            <ScrubableNumber
              :modelValue="getPropertyValue('Path Offset') ?? textData.pathOffset ?? 0"
              @update:modelValue="v => updateAnimatable('Path Offset', v)"
              :min="-100"
              :max="200"
              :precision="1"
            />
            <button
              class="keyframe-btn"
              :class="{ active: isPropertyAnimated('Path Offset') }"
              @click="toggleKeyframe('Path Offset')"
              title="Add keyframe"
            >◆</button>
         </div>

         <div class="row">
            <label>First Margin</label>
            <ScrubableNumber
              :modelValue="getPropertyValue('First Margin') ?? textData.pathFirstMargin ?? 0"
              @update:modelValue="v => updateAnimatable('First Margin', v)"
              :min="0"
            />
         </div>

         <div class="row">
            <label>Last Margin</label>
            <ScrubableNumber
              :modelValue="getPropertyValue('Last Margin') ?? textData.pathLastMargin ?? 0"
              @update:modelValue="v => updateAnimatable('Last Margin', v)"
              :min="0"
            />
         </div>

         <div class="row checkbox-row">
            <label>
              <input type="checkbox" :checked="textData.pathReversed" @change="updateData('pathReversed', !textData.pathReversed)" />
              Reverse Path
            </label>
         </div>

         <div class="row checkbox-row">
            <label>
              <input type="checkbox" :checked="textData.pathPerpendicularToPath ?? true" @change="updateData('pathPerpendicularToPath', !textData.pathPerpendicularToPath)" />
              Perpendicular to Path
            </label>
         </div>

         <div class="row checkbox-row">
            <label>
              <input type="checkbox" :checked="textData.pathForceAlignment" @change="updateData('pathForceAlignment', !textData.pathForceAlignment)" />
              Force Alignment
            </label>
         </div>
       </template>
    </div>

    <div class="prop-section">
       <div class="section-title">Advanced</div>
       <div class="row">
          <label>Tracking</label>
          <ScrubableNumber :modelValue="getPropertyValue('Tracking') || textData.tracking || 0" @update:modelValue="v => updateAnimatable('Tracking', v)" />
       </div>
       <div class="row">
          <label>Line Spacing</label>
          <ScrubableNumber :modelValue="getPropertyValue('Line Spacing') || textData.lineSpacing || 0" @update:modelValue="v => updateAnimatable('Line Spacing', v)" />
       </div>
       <div class="row">
          <label>Baseline</label>
          <ScrubableNumber :modelValue="getPropertyValue('Baseline Shift') || textData.baselineShift || 0" @update:modelValue="v => updateAnimatable('Baseline Shift', v)" />
       </div>
       <div class="row">
          <label>Char Offset</label>
          <ScrubableNumber :modelValue="getPropertyValue('Character Offset') || textData.characterOffset || 0" @update:modelValue="v => updateAnimatable('Character Offset', v)" :precision="0" />
       </div>
       <div class="row text-formatting-row">
          <label>Case</label>
          <div class="format-toggles">
            <button :class="{ active: textData.textCase === 'uppercase' }" @click="toggleCase('uppercase')" title="All Caps">AA</button>
            <button :class="{ active: textData.textCase === 'smallcaps' }" @click="toggleCase('smallcaps')" title="Small Caps">ᴀᴀ</button>
            <button :class="{ active: textData.textCase === 'normal' || !textData.textCase }" @click="toggleCase('normal')" title="Normal">Aa</button>
          </div>
       </div>
       <div class="row text-formatting-row">
          <label>Script</label>
          <div class="format-toggles">
            <button :class="{ active: textData.verticalAlign === 'super' }" @click="toggleVerticalAlign('super')" title="Superscript">X²</button>
            <button :class="{ active: textData.verticalAlign === 'sub' }" @click="toggleVerticalAlign('sub')" title="Subscript">X₂</button>
            <button :class="{ active: textData.verticalAlign === 'baseline' || !textData.verticalAlign }" @click="toggleVerticalAlign('baseline')" title="Normal">X</button>
          </div>
       </div>
    </div>

    <div class="prop-section">
      <div class="section-title">OpenType</div>
      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="textData.kerning !== false" @change="updateData('kerning', !textData.kerning)" />
          Kerning
        </label>
        <span class="feature-tag" :class="{ active: textData.kerning !== false }">kern</span>
      </div>
      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="textData.ligatures !== false" @change="updateData('ligatures', !textData.ligatures)" />
          Ligatures
        </label>
        <span class="feature-tag" :class="{ active: textData.ligatures !== false }">liga</span>
      </div>
      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="textData.discretionaryLigatures" @change="updateData('discretionaryLigatures', !textData.discretionaryLigatures)" />
          Discretionary Ligatures
        </label>
        <span class="feature-tag" :class="{ active: textData.discretionaryLigatures }">dlig</span>
      </div>
      <div class="row checkbox-row">
        <label>
          <input type="checkbox" :checked="textData.smallCapsFeature" @change="updateData('smallCapsFeature', !textData.smallCapsFeature)" />
          Small Caps
        </label>
        <span class="feature-tag" :class="{ active: textData.smallCapsFeature }">smcp</span>
      </div>
      <div class="opentype-info">
        <span class="info-icon">ℹ</span>
        Kerning is active. Ligatures and advanced features require harfbuzz.js (planned).
      </div>
    </div>

    <div class="prop-section">
      <div class="section-title">Paragraph</div>
      <div class="row">
         <label>First Line Indent</label>
         <ScrubableNumber :modelValue="textData.firstLineIndent || 0" @update:modelValue="v => updateData('firstLineIndent', v)" :min="-500" :max="500" />
      </div>
      <div class="row">
         <label>Space Before</label>
         <ScrubableNumber :modelValue="textData.spaceBefore || 0" @update:modelValue="v => updateData('spaceBefore', v)" :min="0" :max="500" />
      </div>
      <div class="row">
         <label>Space After</label>
         <ScrubableNumber :modelValue="textData.spaceAfter || 0" @update:modelValue="v => updateData('spaceAfter', v)" :min="0" :max="500" />
      </div>
    </div>

    <div class="prop-section checkbox">
       <label>
         <input type="checkbox" :checked="textData.perCharacter3D" @change="updateData('perCharacter3D', !textData.perCharacter3D)" />
         Enable Per-Character 3D
       </label>
    </div>

    <!-- Text Animators Section -->
    <div class="prop-section animators-section">
      <div class="section-header">
        <div class="section-title">Animators</div>
        <div class="animator-add-controls">
          <select v-model="selectedPreset" class="preset-select">
            <option value="">Add Preset...</option>
            <option v-for="preset in animatorPresets" :key="preset.type" :value="preset.type">
              {{ preset.name }}
            </option>
          </select>
          <button class="add-btn" @click="addAnimator(selectedPreset || undefined); selectedPreset = ''" title="Add Animator">+</button>
        </div>
      </div>

      <div v-if="animators.length === 0" class="no-animators">
        No animators. Add one to animate text per-character.
      </div>

      <div v-for="animator in animators" :key="animator.id" class="animator-item">
        <div class="animator-header" @click="toggleAnimatorExpanded(animator.id)">
          <span class="expand-icon">{{ expandedAnimators.has(animator.id) ? '▼' : '▶' }}</span>
          <input
            type="checkbox"
            :checked="animator.enabled"
            @click.stop="toggleAnimatorEnabled(animator.id)"
            class="animator-enabled"
          />
          <input
            type="text"
            :value="animator.name"
            @input="e => updateAnimatorName(animator.id, (e.target as HTMLInputElement).value)"
            @click.stop
            class="animator-name"
          />
          <div class="animator-actions">
            <button @click.stop="duplicateAnimator(animator.id)" title="Duplicate">⧉</button>
            <button @click.stop="removeAnimator(animator.id)" title="Remove">×</button>
          </div>
        </div>

        <div v-if="expandedAnimators.has(animator.id)" class="animator-content">
          <!-- Range Selector -->
          <div class="subsection">
            <div class="subsection-title">Range Selector</div>

            <div class="row">
              <label>Based On</label>
              <select
                :value="animator.rangeSelector.basedOn"
                @change="e => updateRangeSelector(animator.id, 'basedOn', (e.target as HTMLSelectElement).value)"
                class="full-select"
              >
                <option value="characters">Characters</option>
                <option value="words">Words</option>
                <option value="lines">Lines</option>
              </select>
            </div>

            <div class="row">
              <label>Start %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.start.value"
                @update:modelValue="v => updateRangeSelector(animator.id, 'start', v)"
                :min="0"
                :max="100"
                :precision="1"
              />
            </div>

            <div class="row">
              <label>End %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.end.value"
                @update:modelValue="v => updateRangeSelector(animator.id, 'end', v)"
                :min="0"
                :max="100"
                :precision="1"
              />
            </div>

            <div class="row">
              <label>Offset %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.offset.value"
                @update:modelValue="v => updateRangeSelector(animator.id, 'offset', v)"
                :min="-100"
                :max="100"
                :precision="1"
              />
            </div>

            <div class="row">
              <label>Shape</label>
              <select
                :value="animator.rangeSelector.shape"
                @change="e => updateRangeSelector(animator.id, 'shape', (e.target as HTMLSelectElement).value)"
                class="full-select"
              >
                <option value="square">Square</option>
                <option value="ramp_up">Ramp Up</option>
                <option value="ramp_down">Ramp Down</option>
                <option value="triangle">Triangle</option>
                <option value="round">Round</option>
                <option value="smooth">Smooth</option>
              </select>
            </div>

            <div class="row checkbox-row">
              <label>
                <input
                  type="checkbox"
                  :checked="animator.rangeSelector.randomizeOrder"
                  @change="updateRangeSelector(animator.id, 'randomizeOrder', !animator.rangeSelector.randomizeOrder)"
                />
                Randomize Order
              </label>
            </div>

            <!-- Advanced Range Selector Options -->
            <div class="row">
              <label>Mode</label>
              <select
                :value="animator.rangeSelector.selectorMode || 'add'"
                @change="e => updateRangeSelector(animator.id, 'selectorMode', (e.target as HTMLSelectElement).value)"
                class="full-select"
              >
                <option value="add">Add</option>
                <option value="subtract">Subtract</option>
                <option value="intersect">Intersect</option>
                <option value="min">Min</option>
                <option value="max">Max</option>
                <option value="difference">Difference</option>
              </select>
            </div>

            <div class="row">
              <label>Amount %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.amount ?? 100"
                @update:modelValue="v => updateRangeSelector(animator.id, 'amount', v)"
                :min="0"
                :max="100"
                :precision="0"
              />
            </div>

            <div class="row">
              <label>Smoothness %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.smoothness ?? 100"
                @update:modelValue="v => updateRangeSelector(animator.id, 'smoothness', v)"
                :min="0"
                :max="100"
                :precision="0"
              />
            </div>

            <div class="row">
              <label>Ease High %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.ease?.high ?? 100"
                @update:modelValue="v => updateRangeSelector(animator.id, 'ease', { ...animator.rangeSelector.ease, high: v })"
                :min="0"
                :max="100"
                :precision="0"
              />
            </div>

            <div class="row">
              <label>Ease Low %</label>
              <ScrubableNumber
                :modelValue="animator.rangeSelector.ease?.low ?? 0"
                @update:modelValue="v => updateRangeSelector(animator.id, 'ease', { ...animator.rangeSelector.ease, low: v })"
                :min="0"
                :max="100"
                :precision="0"
              />
            </div>
          </div>

          <!-- Wiggly Selector -->
          <div class="subsection">
            <div class="subsection-title">
              <label class="section-toggle">
                <input
                  type="checkbox"
                  :checked="animator.wigglySelector?.enabled"
                  @change="toggleWigglySelector(animator.id)"
                />
                Wiggly Selector
              </label>
            </div>

            <template v-if="animator.wigglySelector?.enabled">
              <div class="row">
                <label>Mode</label>
                <select
                  :value="animator.wigglySelector.mode || 'add'"
                  @change="e => updateWigglySelector(animator.id, 'mode', (e.target as HTMLSelectElement).value)"
                  class="full-select"
                >
                  <option value="add">Add</option>
                  <option value="subtract">Subtract</option>
                  <option value="intersect">Intersect</option>
                  <option value="min">Min</option>
                  <option value="max">Max</option>
                  <option value="difference">Difference</option>
                </select>
              </div>

              <div class="row">
                <label>Max Amount %</label>
                <ScrubableNumber
                  :modelValue="animator.wigglySelector.maxAmount ?? 100"
                  @update:modelValue="v => updateWigglySelector(animator.id, 'maxAmount', v)"
                  :min="0"
                  :max="200"
                  :precision="0"
                />
              </div>

              <div class="row">
                <label>Min Amount %</label>
                <ScrubableNumber
                  :modelValue="animator.wigglySelector.minAmount ?? 0"
                  @update:modelValue="v => updateWigglySelector(animator.id, 'minAmount', v)"
                  :min="0"
                  :max="200"
                  :precision="0"
                />
              </div>

              <div class="row">
                <label>Wiggles/Sec</label>
                <ScrubableNumber
                  :modelValue="animator.wigglySelector.wigglesPerSecond ?? 2"
                  @update:modelValue="v => updateWigglySelector(animator.id, 'wigglesPerSecond', v)"
                  :min="0.1"
                  :max="20"
                  :precision="1"
                />
              </div>

              <div class="row">
                <label>Correlation %</label>
                <ScrubableNumber
                  :modelValue="animator.wigglySelector.correlation ?? 50"
                  @update:modelValue="v => updateWigglySelector(animator.id, 'correlation', v)"
                  :min="0"
                  :max="100"
                  :precision="0"
                />
              </div>

              <div class="row checkbox-row">
                <label>
                  <input
                    type="checkbox"
                    :checked="animator.wigglySelector.lockDimensions"
                    @change="updateWigglySelector(animator.id, 'lockDimensions', !animator.wigglySelector.lockDimensions)"
                  />
                  Lock Dimensions
                </label>
              </div>

              <div class="row">
                <label>Based On</label>
                <select
                  :value="animator.wigglySelector.basedOn || 'characters'"
                  @change="e => updateWigglySelector(animator.id, 'basedOn', (e.target as HTMLSelectElement).value)"
                  class="full-select"
                >
                  <option value="characters">Characters</option>
                  <option value="words">Words</option>
                  <option value="lines">Lines</option>
                </select>
              </div>

              <div class="row">
                <label>Random Seed</label>
                <ScrubableNumber
                  :modelValue="animator.wigglySelector.randomSeed ?? 12345"
                  @update:modelValue="v => updateWigglySelector(animator.id, 'randomSeed', Math.floor(v))"
                  :min="0"
                  :max="99999"
                  :precision="0"
                />
              </div>
            </template>
          </div>

          <!-- Expression Selector -->
          <div class="subsection">
            <div class="subsection-title">
              <label class="section-toggle">
                <input
                  type="checkbox"
                  :checked="animator.expressionSelector?.enabled"
                  @change="toggleExpressionSelector(animator.id)"
                />
                Expression Selector
              </label>
            </div>

            <template v-if="animator.expressionSelector?.enabled">
              <div class="row">
                <label>Mode</label>
                <select
                  :value="animator.expressionSelector.mode || 'add'"
                  @change="e => updateExpressionSelector(animator.id, 'mode', (e.target as HTMLSelectElement).value)"
                  class="full-select"
                >
                  <option value="add">Add</option>
                  <option value="subtract">Subtract</option>
                  <option value="intersect">Intersect</option>
                  <option value="min">Min</option>
                  <option value="max">Max</option>
                  <option value="difference">Difference</option>
                </select>
              </div>

              <div class="row">
                <label>Preset</label>
                <select
                  @change="e => { const val = (e.target as HTMLSelectElement).value; if (val) applyExpressionPreset(animator.id, val); (e.target as HTMLSelectElement).value = ''; }"
                  class="full-select"
                >
                  <option value="">Apply Preset...</option>
                  <option v-for="preset in expressionPresetList" :key="preset.key" :value="preset.key">
                    {{ preset.label }}
                  </option>
                </select>
              </div>

              <div class="row">
                <label>Based On</label>
                <select
                  :value="animator.expressionSelector.basedOn || 'characters'"
                  @change="e => updateExpressionSelector(animator.id, 'basedOn', (e.target as HTMLSelectElement).value)"
                  class="full-select"
                >
                  <option value="characters">Characters</option>
                  <option value="words">Words</option>
                  <option value="lines">Lines</option>
                </select>
              </div>

              <div class="row expression-row">
                <label>Expression</label>
                <textarea
                  :value="animator.expressionSelector.amountExpression || ''"
                  @input="e => updateExpressionSelector(animator.id, 'amountExpression', (e.target as HTMLTextAreaElement).value)"
                  class="expression-textarea"
                  placeholder="e.g., textIndex / textTotal * 100"
                  rows="3"
                ></textarea>
              </div>

              <div class="expression-help">
                <div class="help-title">Available Variables:</div>
                <code>textIndex</code> - Current character index (0-based)<br>
                <code>textTotal</code> - Total character count<br>
                <code>selectorValue</code> - Range selector output (0-100)<br>
                <code>time</code> - Current time in seconds<br>
                <code>frame</code> - Current frame number
              </div>
            </template>
          </div>

          <!-- Animator Properties -->
          <div class="subsection">
            <div class="subsection-title">Properties</div>

            <!-- Position -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'position')"
                  @change="updateAnimatorProperty(animator.id, 'position', hasAnimatorProperty(animator, 'position') ? null : { x: 0, y: 0 })"
                />
                Position
              </label>
              <template v-if="hasAnimatorProperty(animator, 'position')">
                <div class="vec2">
                  <ScrubableNumber
                    :modelValue="getAnimatorPropertyValue(animator, 'position')?.x ?? 0"
                    @update:modelValue="v => updateAnimatorProperty(animator.id, 'position', { ...getAnimatorPropertyValue(animator, 'position'), x: v })"
                  />
                  <ScrubableNumber
                    :modelValue="getAnimatorPropertyValue(animator, 'position')?.y ?? 0"
                    @update:modelValue="v => updateAnimatorProperty(animator.id, 'position', { ...getAnimatorPropertyValue(animator, 'position'), y: v })"
                  />
                </div>
              </template>
            </div>

            <!-- Scale -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'scale')"
                  @change="updateAnimatorProperty(animator.id, 'scale', hasAnimatorProperty(animator, 'scale') ? null : { x: 100, y: 100 })"
                />
                Scale %
              </label>
              <template v-if="hasAnimatorProperty(animator, 'scale')">
                <div class="vec2">
                  <ScrubableNumber
                    :modelValue="getAnimatorPropertyValue(animator, 'scale')?.x ?? 100"
                    @update:modelValue="v => updateAnimatorProperty(animator.id, 'scale', { ...getAnimatorPropertyValue(animator, 'scale'), x: v })"
                  />
                  <ScrubableNumber
                    :modelValue="getAnimatorPropertyValue(animator, 'scale')?.y ?? 100"
                    @update:modelValue="v => updateAnimatorProperty(animator.id, 'scale', { ...getAnimatorPropertyValue(animator, 'scale'), y: v })"
                  />
                </div>
              </template>
            </div>

            <!-- Rotation -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'rotation')"
                  @change="updateAnimatorProperty(animator.id, 'rotation', hasAnimatorProperty(animator, 'rotation') ? null : 0)"
                />
                Rotation
              </label>
              <template v-if="hasAnimatorProperty(animator, 'rotation')">
                <ScrubableNumber
                  :modelValue="getAnimatorPropertyValue(animator, 'rotation') ?? 0"
                  @update:modelValue="v => updateAnimatorProperty(animator.id, 'rotation', v)"
                  :min="-360"
                  :max="360"
                />
              </template>
            </div>

            <!-- Opacity -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'opacity')"
                  @change="updateAnimatorProperty(animator.id, 'opacity', hasAnimatorProperty(animator, 'opacity') ? null : 100)"
                />
                Opacity
              </label>
              <template v-if="hasAnimatorProperty(animator, 'opacity')">
                <ScrubableNumber
                  :modelValue="getAnimatorPropertyValue(animator, 'opacity') ?? 100"
                  @update:modelValue="v => updateAnimatorProperty(animator.id, 'opacity', v)"
                  :min="0"
                  :max="100"
                />
              </template>
            </div>

            <!-- Blur -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'blur')"
                  @change="updateAnimatorProperty(animator.id, 'blur', hasAnimatorProperty(animator, 'blur') ? null : { x: 0, y: 0 })"
                />
                Blur
              </label>
              <template v-if="hasAnimatorProperty(animator, 'blur')">
                <div class="vec2">
                  <ScrubableNumber
                    :modelValue="getAnimatorPropertyValue(animator, 'blur')?.x ?? 0"
                    @update:modelValue="v => updateAnimatorProperty(animator.id, 'blur', { ...getAnimatorPropertyValue(animator, 'blur'), x: v })"
                    :min="0"
                    :max="100"
                  />
                  <ScrubableNumber
                    :modelValue="getAnimatorPropertyValue(animator, 'blur')?.y ?? 0"
                    @update:modelValue="v => updateAnimatorProperty(animator.id, 'blur', { ...getAnimatorPropertyValue(animator, 'blur'), y: v })"
                    :min="0"
                    :max="100"
                  />
                </div>
              </template>
            </div>

            <!-- Tracking -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'tracking')"
                  @change="updateAnimatorProperty(animator.id, 'tracking', hasAnimatorProperty(animator, 'tracking') ? null : 0)"
                />
                Tracking
              </label>
              <template v-if="hasAnimatorProperty(animator, 'tracking')">
                <ScrubableNumber
                  :modelValue="getAnimatorPropertyValue(animator, 'tracking') ?? 0"
                  @update:modelValue="v => updateAnimatorProperty(animator.id, 'tracking', v)"
                  :min="-200"
                  :max="200"
                />
              </template>
            </div>

            <!-- Fill Color -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'fillColor')"
                  @change="updateAnimatorProperty(animator.id, 'fillColor', hasAnimatorProperty(animator, 'fillColor') ? null : '#ffffff')"
                />
                Fill Color
              </label>
              <template v-if="hasAnimatorProperty(animator, 'fillColor')">
                <input
                  type="color"
                  :value="getAnimatorPropertyValue(animator, 'fillColor') || '#ffffff'"
                  @input="e => updateAnimatorProperty(animator.id, 'fillColor', (e.target as HTMLInputElement).value)"
                  class="color-input"
                />
              </template>
            </div>

            <!-- Stroke Color -->
            <div class="property-row">
              <label class="prop-label">
                <input
                  type="checkbox"
                  :checked="hasAnimatorProperty(animator, 'strokeColor')"
                  @change="updateAnimatorProperty(animator.id, 'strokeColor', hasAnimatorProperty(animator, 'strokeColor') ? null : '#000000')"
                />
                Stroke Color
              </label>
              <template v-if="hasAnimatorProperty(animator, 'strokeColor')">
                <input
                  type="color"
                  :value="getAnimatorPropertyValue(animator, 'strokeColor') || '#000000'"
                  @input="e => updateAnimatorProperty(animator.id, 'strokeColor', (e.target as HTMLInputElement).value)"
                  class="color-input"
                />
              </template>
            </div>
          </div>
        </div>
      </div>
    </div>
  </div>
</template>

<script setup lang="ts">
import { computed, ref, reactive, onMounted } from 'vue';
import { useCompositorStore } from '@/stores/compositorStore';
import { ScrubableNumber } from '@/components/controls';
import { fontService, type FontCategory } from '@/services/fontService';
import {
  TEXT_ANIMATOR_PRESET_LIST,
  applyTextAnimatorPreset,
  createTextAnimator,
  type TextAnimatorPreset,
} from '@/services/textAnimator';
import type { TextAnimator, TextAnimatorPresetType, TextRangeSelector, TextWigglySelector, TextExpressionSelector } from '@/types/project';
import {
  DEFAULT_WIGGLY_SELECTOR,
  DEFAULT_EXPRESSION_SELECTOR,
  EXPRESSION_PRESETS,
} from '@/services/textAnimator';

const props = defineProps<{ layer: any }>();
const emit = defineEmits(['update']);
const store = useCompositorStore();

// Font loading state
const fontCategories = ref<FontCategory[]>([]);
const hasSystemFonts = ref(false);
const loadingFonts = ref(false);

// Text Animator state
const expandedAnimators = ref<Set<string>>(new Set());
const selectedPreset = ref<TextAnimatorPresetType | ''>('');
const animatorPresets = TEXT_ANIMATOR_PRESET_LIST;

onMounted(async () => {
  await fontService.initialize();
  fontCategories.value = fontService.getFontCategories();
  hasSystemFonts.value = fontService.hasSystemFonts();
});

// Request system font access (requires user interaction)
async function requestFontAccess() {
  loadingFonts.value = true;
  try {
    const success = await fontService.requestSystemFontAccess();
    if (success) {
      fontCategories.value = fontService.getFontCategories();
      hasSystemFonts.value = true;
    }
  } finally {
    loadingFonts.value = false;
  }
}

const textData = computed(() => props.layer.data);
const transform = computed(() => props.layer.transform);
// Include both visible spline layers AND invisible path layers as potential text paths
// Users can put text on a logo shape (spline) or an invisible motion guide (path)
const splineLayers = computed(() => store.layers.filter(l => l.type === 'spline' || l.type === 'path'));
const animators = computed<TextAnimator[]>(() => textData.value.animators || []);

// Text Animator functions
function toggleAnimatorExpanded(animatorId: string) {
  if (expandedAnimators.value.has(animatorId)) {
    expandedAnimators.value.delete(animatorId);
  } else {
    expandedAnimators.value.add(animatorId);
  }
}

function addAnimator(presetType?: TextAnimatorPresetType) {
  const newAnimator = presetType
    ? applyTextAnimatorPreset(presetType, 45)
    : createTextAnimator(`Animator ${animators.value.length + 1}`);

  const currentAnimators = [...animators.value, newAnimator];
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  expandedAnimators.value.add(newAnimator.id);
  emit('update');
}

function removeAnimator(animatorId: string) {
  const currentAnimators = animators.value.filter(a => a.id !== animatorId);
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  expandedAnimators.value.delete(animatorId);
  emit('update');
}

function duplicateAnimator(animatorId: string) {
  const source = animators.value.find(a => a.id === animatorId);
  if (!source) return;

  const duplicated: TextAnimator = structuredClone(source);
  duplicated.id = `animator_${Date.now()}_${Math.random().toString(36).substr(2, 5)}`;
  duplicated.name = `${source.name} (Copy)`;

  const currentAnimators = [...animators.value, duplicated];
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  expandedAnimators.value.add(duplicated.id);
  emit('update');
}

function toggleAnimatorEnabled(animatorId: string) {
  const animator = animators.value.find(a => a.id === animatorId);
  if (!animator) return;

  const currentAnimators = animators.value.map(a =>
    a.id === animatorId ? { ...a, enabled: !a.enabled } : a
  );
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function updateAnimatorName(animatorId: string, name: string) {
  const currentAnimators = animators.value.map(a =>
    a.id === animatorId ? { ...a, name } : a
  );
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function updateRangeSelector(animatorId: string, key: keyof TextRangeSelector, value: any) {
  const currentAnimators = animators.value.map(a => {
    if (a.id !== animatorId) return a;
    const updated = { ...a };
    if (key === 'start' || key === 'end' || key === 'offset') {
      // Update animatable property value
      updated.rangeSelector = {
        ...updated.rangeSelector,
        [key]: {
          ...updated.rangeSelector[key],
          value
        }
      };
    } else {
      updated.rangeSelector = {
        ...updated.rangeSelector,
        [key]: value
      };
    }
    return updated;
  });
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function updateAnimatorProperty(animatorId: string, propKey: string, value: any) {
  const currentAnimators = animators.value.map(a => {
    if (a.id !== animatorId) return a;
    const updated = { ...a };

    if (value === null || value === undefined) {
      // Remove property
      const { [propKey]: removed, ...rest } = updated.properties;
      updated.properties = rest;
    } else {
      // Add or update property
      updated.properties = {
        ...updated.properties,
        [propKey]: {
          id: `prop_${Date.now()}`,
          name: propKey.charAt(0).toUpperCase() + propKey.slice(1),
          type: typeof value === 'number' ? 'number' : 'object',
          value,
          animated: false,
          keyframes: []
        }
      };
    }
    return updated;
  });
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function getAnimatorPropertyValue(animator: TextAnimator, propKey: string): any {
  return animator.properties[propKey]?.value;
}

function hasAnimatorProperty(animator: TextAnimator, propKey: string): boolean {
  return propKey in animator.properties;
}

// Wiggly Selector functions
function toggleWigglySelector(animatorId: string) {
  const currentAnimators = animators.value.map(a => {
    if (a.id !== animatorId) return a;
    const updated = { ...a };
    if (updated.wigglySelector?.enabled) {
      // Disable
      updated.wigglySelector = { ...updated.wigglySelector, enabled: false };
    } else {
      // Enable (create if doesn't exist)
      updated.wigglySelector = updated.wigglySelector
        ? { ...updated.wigglySelector, enabled: true }
        : { ...DEFAULT_WIGGLY_SELECTOR, enabled: true };
    }
    return updated;
  });
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function updateWigglySelector(animatorId: string, key: keyof TextWigglySelector, value: any) {
  const currentAnimators = animators.value.map(a => {
    if (a.id !== animatorId) return a;
    const updated = { ...a };
    updated.wigglySelector = {
      ...(updated.wigglySelector || DEFAULT_WIGGLY_SELECTOR),
      [key]: value
    };
    return updated;
  });
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

// Expression Selector functions
function toggleExpressionSelector(animatorId: string) {
  const currentAnimators = animators.value.map(a => {
    if (a.id !== animatorId) return a;
    const updated = { ...a };
    if (updated.expressionSelector?.enabled) {
      // Disable
      updated.expressionSelector = { ...updated.expressionSelector, enabled: false };
    } else {
      // Enable (create if doesn't exist)
      updated.expressionSelector = updated.expressionSelector
        ? { ...updated.expressionSelector, enabled: true }
        : { ...DEFAULT_EXPRESSION_SELECTOR, enabled: true };
    }
    return updated;
  });
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function updateExpressionSelector(animatorId: string, key: keyof TextExpressionSelector, value: any) {
  const currentAnimators = animators.value.map(a => {
    if (a.id !== animatorId) return a;
    const updated = { ...a };
    updated.expressionSelector = {
      ...(updated.expressionSelector || DEFAULT_EXPRESSION_SELECTOR),
      [key]: value
    };
    return updated;
  });
  store.updateLayerData(props.layer.id, { animators: currentAnimators });
  emit('update');
}

function applyExpressionPreset(animatorId: string, presetKey: string) {
  const expression = EXPRESSION_PRESETS[presetKey as keyof typeof EXPRESSION_PRESETS];
  if (expression) {
    updateExpressionSelector(animatorId, 'amountExpression', expression);
  }
}

// Expression presets list for dropdown
const expressionPresetList = Object.entries(EXPRESSION_PRESETS).map(([key, value]) => ({
  key,
  label: key.replace(/([A-Z])/g, ' $1').replace(/^./, str => str.toUpperCase()),
  expression: value
}));

function getProperty(name: string) {
    return props.layer.properties?.find((p: any) => p.name === name);
}

function getPropertyValue(name: string) {
    const p = getProperty(name);
    return p ? p.value : null;
}

function updateText(val: string) {
    // Use store action to update text property
    store.setPropertyValue(props.layer.id, 'Source Text', val);
    // Also update the layer data directly for immediate render
    store.updateLayerData(props.layer.id, { text: val });
    emit('update');
}

function updateData(key: string, val: any) {
    // Use store action to update layer data
    store.updateLayerData(props.layer.id, { [key]: val });

    // Sync to animatable property via store
    const map: Record<string, string> = {
        'fill': 'Fill Color',
        'stroke': 'Stroke Color',
        'fontSize': 'Font Size',
        'strokeWidth': 'Stroke Width'
    };
    if (map[key]) {
        store.setPropertyValue(props.layer.id, map[key], val);
    }
    emit('update');
}

function updateAnimatable(name: string, val: number) {
    // Use store action to update property value
    store.setPropertyValue(props.layer.id, name, val);

    // Also update static data for immediate render via store
    const keyMap: Record<string, string> = {
        'Font Size': 'fontSize',
        'Stroke Width': 'strokeWidth',
        'Tracking': 'tracking',
        'Line Spacing': 'lineSpacing',
        'Baseline Shift': 'baselineShift',
        'Character Offset': 'characterOffset',
        'Path Offset': 'pathOffset',
        'First Margin': 'pathFirstMargin',
        'Last Margin': 'pathLastMargin'
    };
    if (keyMap[name]) {
        store.updateLayerData(props.layer.id, { [keyMap[name]]: val });
    }
    emit('update');
}

function isPropertyAnimated(name: string): boolean {
    const prop = getProperty(name);
    return prop?.animated ?? false;
}

function toggleKeyframe(name: string) {
    const prop = getProperty(name);
    if (!prop) return;

    const currentFrame = store.currentFrame;

    // Check if keyframe exists at current frame
    const existingKf = prop.keyframes?.find((kf: any) => kf.frame === currentFrame);

    if (existingKf) {
        // Remove keyframe via store
        store.removeKeyframe(props.layer.id, name, existingKf.id);
    } else {
        // Add keyframe at current frame via store
        store.addKeyframe(props.layer.id, name, prop.value, currentFrame);
    }

    emit('update');
}

function updateTransform(propName: string, axis: string | null, val: number) {
    const prop = transform.value[propName];
    let newValue: any;
    if (axis) {
        newValue = { ...prop.value, [axis]: val };
    } else {
        newValue = val;
    }
    // Use store action to update transform property
    store.setPropertyValue(props.layer.id, `transform.${propName}`, newValue);
    emit('update');
}

function updateOpacity(val: number) {
    // Use store action to update opacity
    store.setPropertyValue(props.layer.id, 'opacity', val);
    emit('update');
}

function toggleBold() {
    updateData('fontWeight', textData.value.fontWeight === 'bold' ? '400' : 'bold');
}
function toggleItalic() {
    updateData('fontStyle', textData.value.fontStyle === 'italic' ? 'normal' : 'italic');
}

function toggleCase(caseType: 'uppercase' | 'smallcaps' | 'normal') {
    updateData('textCase', caseType);
}

function toggleVerticalAlign(align: 'super' | 'sub' | 'baseline') {
    updateData('verticalAlign', align);
}

// Handle font change - ensure Google fonts are loaded
async function handleFontChange(family: string) {
    // Ensure the font is loaded before applying
    await fontService.ensureFont(family);
    updateData('fontFamily', family);
}
</script>

<style scoped>
.text-properties { padding: 15px; color: #ddd; font-family: 'Segoe UI', sans-serif; font-size: 13px; overflow-y: auto; }
.prop-section { margin-bottom: 20px; border-bottom: 1px solid #333; padding-bottom: 10px; }
.section-title { font-weight: bold; margin-bottom: 10px; color: #888; font-size: 13px; text-transform: uppercase; }

.row { display: flex; align-items: center; margin-bottom: 8px; gap: 10px; }
.row label { width: 80px; color: #aaa; flex-shrink: 0; }

.text-area { width: 100%; background: #222; border: 1px solid #444; color: #fff; padding: 8px; font-family: sans-serif; resize: vertical; border-radius: 3px; }
.text-area:focus { border-color: #4a90d9; outline: none; }

.font-select, .full-select { flex: 1; background: #222; color: #fff; border: 1px solid #444; padding: 6px; border-radius: 3px; max-width: 200px; }
.font-select:focus, .full-select:focus { border-color: #4a90d9; outline: none; }
.font-select optgroup { color: #888; font-style: normal; background: #1a1a1a; }
.font-select option { color: #fff; background: #222; padding: 4px; }

.font-row { flex-wrap: nowrap; }

.font-access-btn {
  flex: 1;
  background: #333;
  border: 1px dashed #555;
  color: #888;
  padding: 8px 12px;
  border-radius: 3px;
  cursor: pointer;
  font-size: 13px;
  transition: all 0.2s;
}
.font-access-btn:hover:not(:disabled) { background: #444; color: #aaa; border-color: #666; }
.font-access-btn:disabled { cursor: not-allowed; opacity: 0.6; }

.style-toggles { display: flex; gap: 2px; }
.style-toggles button { background: #333; border: 1px solid #444; color: #aaa; width: 28px; height: 28px; cursor: pointer; font-weight: bold; border-radius: 3px; }
.style-toggles button.active { background: #4a90d9; color: #fff; border-color: #4a90d9; }
.style-toggles button:hover:not(.active) { background: #444; }

.color-row { justify-content: flex-start; gap: 20px; }
.color-item { display: flex; align-items: center; gap: 8px; }
.color-item input[type="color"] { width: 32px; height: 28px; border: 1px solid #444; padding: 0; cursor: pointer; border-radius: 3px; background: #222; }
.color-item span { color: #aaa; font-size: 12px; }

.align-buttons { display: flex; background: #222; border: 1px solid #444; border-radius: 3px; overflow: hidden; }
.align-buttons button { flex: 1; background: transparent; border: none; color: #666; padding: 6px 12px; cursor: pointer; font-size: 12px; border-right: 1px solid #444; }
.align-buttons button:last-child { border-right: none; }
.align-buttons button.active { background: #4a90d9; color: #fff; }
.align-buttons button:hover:not(.active) { background: #333; color: #fff; }

.vec2 { display: flex; gap: 5px; flex: 1; }

.checkbox label { display: flex; align-items: center; gap: 10px; cursor: pointer; color: #eee; font-size: 13px; }
.checkbox input[type="checkbox"] { width: 16px; height: 16px; cursor: pointer; }

.checkbox-row label { display: flex; align-items: center; gap: 8px; cursor: pointer; color: #ddd; font-size: 12px; width: auto; }
.checkbox-row input[type="checkbox"] { width: 14px; height: 14px; cursor: pointer; }

.keyframe-btn {
  background: #333;
  border: 1px solid #444;
  color: #666;
  width: 24px;
  height: 24px;
  cursor: pointer;
  border-radius: 3px;
  font-size: 12px;
  display: flex;
  align-items: center;
  justify-content: center;
  flex-shrink: 0;
}
.keyframe-btn:hover { background: #444; color: #888; }
.keyframe-btn.active { background: #b38600; color: #fff; border-color: #b38600; }

.text-formatting-row { gap: 8px; }
.format-toggles { display: flex; background: #222; border: 1px solid #444; border-radius: 3px; overflow: hidden; }
.format-toggles button {
  background: transparent;
  border: none;
  color: #888;
  padding: 6px 10px;
  cursor: pointer;
  font-size: 13px;
  border-right: 1px solid #444;
  min-width: 32px;
}
.format-toggles button:last-child { border-right: none; }
.format-toggles button.active { background: #4a90d9; color: #fff; }
.format-toggles button:hover:not(.active) { background: #333; color: #fff; }

/* Text Animators Section */
.animators-section { border-bottom: none; }

.section-header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 12px;
}

.animator-add-controls {
  display: flex;
  gap: 4px;
}

.preset-select {
  background: #222;
  border: 1px solid #444;
  color: #aaa;
  padding: 4px 8px;
  border-radius: 3px;
  font-size: 11px;
  max-width: 130px;
}
.preset-select:focus { border-color: #4a90d9; outline: none; }

.add-btn {
  background: #4a90d9;
  border: none;
  color: #fff;
  width: 24px;
  height: 24px;
  border-radius: 3px;
  cursor: pointer;
  font-size: 16px;
  font-weight: bold;
  line-height: 1;
}
.add-btn:hover { background: #5a9fe9; }

.no-animators {
  color: #666;
  font-size: 12px;
  font-style: italic;
  padding: 12px;
  text-align: center;
  background: #1a1a1a;
  border-radius: 4px;
}

.animator-item {
  background: #1e1e1e;
  border: 1px solid #333;
  border-radius: 4px;
  margin-bottom: 8px;
  overflow: hidden;
}

.animator-header {
  display: flex;
  align-items: center;
  padding: 8px 10px;
  cursor: pointer;
  gap: 8px;
  background: #252525;
}
.animator-header:hover { background: #2a2a2a; }

.expand-icon {
  color: #666;
  font-size: 10px;
  width: 12px;
}

.animator-enabled {
  width: 14px;
  height: 14px;
  cursor: pointer;
}

.animator-name {
  flex: 1;
  background: transparent;
  border: 1px solid transparent;
  color: #ddd;
  padding: 2px 6px;
  font-size: 12px;
  border-radius: 2px;
}
.animator-name:focus {
  background: #222;
  border-color: #444;
  outline: none;
}

.animator-actions {
  display: flex;
  gap: 2px;
}
.animator-actions button {
  background: transparent;
  border: 1px solid transparent;
  color: #666;
  width: 22px;
  height: 22px;
  cursor: pointer;
  border-radius: 2px;
  font-size: 14px;
}
.animator-actions button:hover {
  background: #333;
  color: #aaa;
  border-color: #444;
}

.animator-content {
  padding: 10px;
  border-top: 1px solid #333;
}

.subsection {
  margin-bottom: 12px;
}
.subsection:last-child { margin-bottom: 0; }

.subsection-title {
  color: #888;
  font-size: 11px;
  text-transform: uppercase;
  margin-bottom: 8px;
  padding-bottom: 4px;
  border-bottom: 1px solid #333;
}

.property-row {
  display: flex;
  align-items: center;
  margin-bottom: 6px;
  gap: 8px;
  min-height: 28px;
}

.prop-label {
  display: flex;
  align-items: center;
  gap: 6px;
  color: #aaa;
  font-size: 12px;
  min-width: 90px;
  cursor: pointer;
}
.prop-label input[type="checkbox"] {
  width: 12px;
  height: 12px;
  cursor: pointer;
}

.color-input {
  width: 50px;
  height: 24px;
  border: 1px solid #444;
  padding: 0;
  cursor: pointer;
  border-radius: 3px;
  background: #222;
}

/* Wiggly & Expression Selector Styles */
.section-toggle {
  display: flex;
  align-items: center;
  gap: 8px;
  cursor: pointer;
  color: #aaa;
  font-size: 11px;
  text-transform: uppercase;
}
.section-toggle input[type="checkbox"] {
  width: 14px;
  height: 14px;
  cursor: pointer;
}

.expression-row {
  flex-direction: column;
  align-items: flex-start;
  gap: 6px;
}
.expression-row label {
  width: auto;
}

.expression-textarea {
  width: 100%;
  min-height: 60px;
  background: #1a1a1a;
  border: 1px solid #444;
  color: #ddd;
  padding: 8px;
  font-family: 'Consolas', 'Monaco', monospace;
  font-size: 11px;
  line-height: 1.4;
  resize: vertical;
  border-radius: 3px;
}
.expression-textarea:focus {
  border-color: #4a90d9;
  outline: none;
}
.expression-textarea::placeholder {
  color: #555;
}

.expression-help {
  background: #1a1a1a;
  border: 1px solid #333;
  border-radius: 3px;
  padding: 8px 10px;
  font-size: 10px;
  color: #666;
  margin-top: 4px;
}
.expression-help .help-title {
  color: #888;
  font-weight: 600;
  margin-bottom: 4px;
}
.expression-help code {
  background: #252525;
  padding: 1px 4px;
  border-radius: 2px;
  color: #8B5CF6;
  font-family: 'Consolas', 'Monaco', monospace;
}

/* OpenType Features Section */
.feature-tag {
  font-family: 'Consolas', 'Monaco', monospace;
  font-size: 10px;
  padding: 2px 6px;
  background: #222;
  border: 1px solid #444;
  border-radius: 3px;
  color: #666;
  text-transform: lowercase;
  margin-left: auto;
}
.feature-tag.active {
  background: #2a3a2a;
  border-color: #4a6a4a;
  color: #8B5CF6;
}

.opentype-info {
  display: flex;
  align-items: flex-start;
  gap: 8px;
  margin-top: 8px;
  padding: 8px 10px;
  background: #1a1a1a;
  border: 1px solid #333;
  border-radius: 4px;
  font-size: 11px;
  color: #666;
  line-height: 1.4;
}
.opentype-info .info-icon {
  color: #4a90d9;
  font-size: 12px;
  flex-shrink: 0;
}
</style>
