# Product Tour Component Research

**Status**: Implementation Phase  
**Target**: Hydrogen UI Framework (Pure PureScript)

**Implementation Started**: 2026-02-24  
**Modules Created**:
- `Hydrogen.Tour.Types` - Core ADTs (TourId, StepId, Target, Placement, TourPhase, etc.)
- `Hydrogen.Tour.Step` - Step configuration types and button definitions
- `Hydrogen.Tour.State` - TourState and TourMsg types
- `Hydrogen.Tour.Update` - State machine update function
- `Hydrogen.Tour.View` - View components (spotlight, tooltip, progress)
- `Hydrogen.Tour.Storage` - Persistence (don't show again, snooze, completion)
- `Hydrogen.Tour` - Leader module with re-exports

────────────────────────────────────────────────────────────────────────────────

## Overview

Research initiative to design the ULTIMATE product tour component for Hydrogen.
This document captures detailed specifications drawn from industry-leading
implementations to inform a type-safe, accessibility-first, pure functional
implementation.

### Reference Implementations Studied

| Library       | Strengths                                    | License    |
|---------------|----------------------------------------------|------------|
| Driver.js     | Lightweight, vanilla JS, good animations     | MIT        |
| Shepherd.js   | Feature-rich, Floating UI integration        | MIT        |
| Intro.js      | Battle-tested, wide adoption                 | AGPL/Comm  |
| React Joyride | React ecosystem, good defaults               | MIT        |
| Flows         | Modern, multi-page tours                     | Proprietary|
| Floating UI   | Best-in-class positioning                    | MIT        |
| Framer Motion | Spring physics, gesture support              | MIT        |

────────────────────────────────────────────────────────────────────────────────
                                                                      // ROUND 1
                                                   // INTERACTION & ANIMATION //
────────────────────────────────────────────────────────────────────────────────

## 1. Highlight Techniques

### 1.1 Spotlight Overlay (Cutout)

The primary technique for drawing attention to target elements. A semi-transparent
overlay covers the entire viewport with a "cutout" revealing the target element.

#### Specification

| Property        | Type              | Default          | Description                         |
|-----------------|-------------------|------------------|-------------------------------------|
| overlayColor    | SRGBA             | rgba(0,0,0,0.75) | Overlay fill color                  |
| overlayOpacity  | Bounded 0.0 1.0   | 0.75             | Overlay transparency                |
| cutoutPadding   | Pixel             | 8px              | Space between target and cutout edge|
| cutoutRadius    | Pixel             | 4px              | Border radius of cutout             |
| cutoutShape     | Shape             | Rectangle        | Rectangle, Circle, or match target  |
| transitionMs    | Milliseconds      | 300              | Morph transition duration           |
| easing          | EasingFunction    | ease-out         | Transition timing function          |

#### Implementation Notes

- Use CSS `mix-blend-mode: multiply` or SVG `<mask>` for cutout
- SVG mask approach provides smoother animations and arbitrary shapes
- Canvas approach offers best performance for complex animations
- Must handle `position: fixed` elements correctly (they escape normal stacking)

### 1.2 Pulsing / Breathing Animation

Subtle animation to draw attention without being distracting.

#### Keyframe Specification

```
@keyframes pulse {
  0%   { transform: scale(1.0);  opacity: 1.0;  box-shadow: 0 0 0 0 accent }
  50%  { transform: scale(1.02); opacity: 0.95; box-shadow: 0 0 0 8px transparent }
  100% { transform: scale(1.0);  opacity: 1.0;  box-shadow: 0 0 0 0 accent }
}
```

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| pulseScale      | Bounded 1.0 1.1   | 1.02       | Maximum scale during pulse     |
| pulseDuration   | Milliseconds      | 2000       | Full cycle duration            |
| pulseDelay      | Milliseconds      | 0          | Delay before animation starts  |
| pulseIterations | Int or Infinite   | Infinite   | Number of cycles               |
| respectsMotion  | Boolean           | true       | Honor prefers-reduced-motion   |

### 1.3 Magnetic Attraction

Element appears to "pull" toward the target with spring physics.

#### Spring Physics Parameters

| Parameter  | Type            | Default | Description                           |
|------------|-----------------|---------|---------------------------------------|
| stiffness  | Bounded 1 1000  | 100     | Spring constant (higher = snappier)   |
| damping    | Bounded 1 100   | 10      | Friction (higher = less oscillation)  |
| mass       | Bounded 0.1 10  | 1       | Inertia (higher = more momentum)      |
| velocity   | Number          | 0       | Initial velocity                      |

#### Presets

| Preset    | Stiffness | Damping | Mass | Character                    |
|-----------|-----------|---------|------|------------------------------|
| gentle    | 120       | 14      | 1    | Soft, professional           |
| snappy    | 300       | 20      | 1    | Quick, responsive            |
| bouncy    | 180       | 12      | 1    | Playful, noticeable          |
| stiff     | 400       | 30      | 1    | Minimal overshoot            |

### 1.4 Morphing Highlights

Smooth transition of highlight shape between steps.

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| morphDuration   | Milliseconds      | 400        | Shape transition duration      |
| morphEasing     | EasingFunction    | ease-in-out| Timing function                |
| interpolation   | Interpolation     | CSS        | CSS transitions or FLIP        |

#### FLIP Technique (First, Last, Invert, Play)

1. **First**: Record initial position/size of highlight
2. **Last**: Move highlight to final position (no transition)
3. **Invert**: Apply transform to make it appear in original position
4. **Play**: Animate transform back to identity

Benefits: Hardware-accelerated, smooth 60fps animations.

### 1.5 Multiple Simultaneous Highlights

For steps that reference multiple related elements.

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| targets         | Array Selector    | []         | Multiple target selectors      |
| primaryIndex    | Int               | 0          | Which target gets the tooltip  |
| connectionLine  | Maybe LineStyle   | Nothing    | Draw lines between targets     |
| groupPadding    | Pixel             | 16         | Padding around group bounds    |

────────────────────────────────────────────────────────────────────────────────

## 2. Tooltip Behaviors

### 2.1 Auto-Positioning with Floating UI

The industry standard for tooltip positioning uses a middleware pipeline.

#### Middleware Stack (Order Matters)

```
offset → flip → shift → arrow → hide
```

| Middleware | Purpose                                          |
|------------|--------------------------------------------------|
| offset     | Add space between tooltip and target (8-12px)    |
| flip       | Switch placement when clipped (top ↔ bottom)     |
| shift      | Slide along axis to stay in viewport             |
| arrow      | Position the arrow/pointer element               |
| hide       | Hide tooltip when target is scrolled out of view |

#### Placement Options

```
     top-start      top       top-end
           ┌─────────────────────┐
left-start │                     │ right-start
left       │      (target)       │ right
left-end   │                     │ right-end
           └─────────────────────┘
  bottom-start   bottom   bottom-end
```

#### Configuration

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| placement       | Placement         | bottom     | Preferred tooltip position     |
| offsetMain      | Pixel             | 12         | Distance from target           |
| offsetCross     | Pixel             | 0          | Cross-axis offset              |
| padding         | Pixel             | 8          | Viewport edge padding          |
| boundary        | Element           | viewport   | Clipping boundary              |
| flipFallbacks   | Array Placement   | auto       | Fallback placements            |

### 2.2 Scroll Following

Tooltip tracks target as page scrolls.

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| followScroll    | Boolean           | true       | Track during scroll            |
| hideOnScroll    | Boolean           | false      | Hide if target leaves viewport |
| scrollThreshold | Pixel             | 50         | Distance before hiding         |
| updateOnScroll  | Throttle          | 16ms       | Position update frequency      |

#### Scroll Detection

- Use `IntersectionObserver` for efficient visibility detection
- Threshold: 0.0, 0.5, 1.0 for granular visibility states
- Fall back to scroll event listener with throttling

### 2.3 Arrow Animations

The pointer/arrow connecting tooltip to target.

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| arrowSize       | Pixel             | 8          | Arrow width/height             |
| arrowOffset     | Pixel             | 0          | Shift along tooltip edge       |
| arrowElement    | Element           | CSS        | Custom arrow element           |
| animateArrow    | Boolean           | true       | Animate on placement change    |

### 2.4 Entry/Exit Transitions

#### Entry Animations

| Animation     | Properties                                      | Duration |
|---------------|-------------------------------------------------|----------|
| fade          | opacity: 0 → 1                                  | 200ms    |
| scale         | transform: scale(0.95) → scale(1)               | 200ms    |
| slide         | transform: translateY(8px) → translateY(0)      | 200ms    |
| combined      | All above simultaneously                        | 250ms    |

#### Exit Animations

Mirror of entry with reversed timing:
- Slightly faster (150-200ms vs 200-250ms)
- Same easing function

#### Reduced Motion

When `prefers-reduced-motion: reduce`:
- Disable scale and slide transforms
- Use opacity-only transitions (150ms)
- No spring physics

### 2.5 Tooltip Chains

Smooth transitions between consecutive tooltips.

#### Transition Modes

| Mode          | Behavior                                        |
|---------------|-------------------------------------------------|
| sequential    | Exit current, then enter next                   |
| crossfade     | Overlap exit/enter with opacity                 |
| morph         | Single tooltip transforms position/content      |
| instant       | No transition, immediate switch                 |

#### Morph Specification (Recommended)

```
1. Animate position (spring physics, 300ms)
2. Crossfade content (opacity, 150ms)
3. Animate size if different (150ms)
```

────────────────────────────────────────────────────────────────────────────────

## 3. Navigation Patterns

### 3.1 Keyboard Shortcuts

Full keyboard accessibility is mandatory (WCAG 2.1 AA).

#### Required Bindings

| Key           | Action                          | Notes                      |
|---------------|---------------------------------|----------------------------|
| Escape        | Dismiss tour                    | WCAG required              |
| Tab           | Focus next interactive element  | Standard browser behavior  |
| Shift+Tab     | Focus previous element          | Standard browser behavior  |
| Enter/Space   | Activate focused button         | Standard browser behavior  |
| ArrowRight    | Next step                       | Optional, common pattern   |
| ArrowLeft     | Previous step                   | Optional, common pattern   |
| Home          | First step                      | Optional                   |
| End           | Last step                       | Optional                   |

#### Focus Management

| Requirement                 | Implementation                              |
|-----------------------------|---------------------------------------------|
| Focus visible               | 2px outline, 3:1 contrast ratio minimum     |
| Focus trap in modal         | Tab cycles within tooltip                   |
| Focus restoration           | Return focus to trigger on dismiss          |
| Skip link                   | "Skip tour" accessible via keyboard         |

### 3.2 Gesture Support (Mobile)

| Gesture       | Action              | Notes                           |
|---------------|---------------------|---------------------------------|
| Tap outside   | Next step or dismiss| Configurable                    |
| Swipe left    | Next step           | Horizontal tours                |
| Swipe right   | Previous step       | Horizontal tours                |
| Swipe down    | Dismiss             | Optional, matches sheet pattern |
| Pinch         | None                | Don't interfere with zoom       |

### 3.3 Progress Indicators

Progress visibility increases completion rates ("see the finish line" effect).

#### Types

| Type          | Visual                          | Best For                   |
|---------------|---------------------------------|----------------------------|
| dots          | ○ ○ ● ○ ○                       | Short tours (< 7 steps)    |
| fraction      | "3 of 7"                        | Medium tours               |
| progress bar  | ████░░░░ 42%                    | Long tours, gamification   |
| steps         | 1 → 2 → [3] → 4 → 5             | Branching tours            |

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| showProgress    | Boolean           | true       | Display progress indicator     |
| progressType    | ProgressType      | dots       | Visual style                   |
| showStepCount   | Boolean           | true       | Show "X of Y"                  |
| clickableDots   | Boolean           | false      | Allow jumping to steps         |

### 3.4 Branching Paths

Conditional navigation based on user choices or context.

#### Specification

| Property        | Type                    | Description                    |
|-----------------|-------------------------|--------------------------------|
| nextStep        | StepId or Condition     | Static or conditional next     |
| branches        | Array Branch            | Multiple possible paths        |
| condition       | State -> Boolean        | Evaluate to determine path     |

#### Branch Definition

```purescript
type Branch =
  { condition :: State -> Boolean
  , targetStep :: StepId
  , label :: String  -- For analytics
  }
```

### 3.5 "Don't Show Again" Functionality

#### Storage Strategy

| Storage         | Scope              | Expiry              | Use Case           |
|-----------------|--------------------|---------------------|--------------------|
| localStorage    | Browser            | Permanent           | General preference |
| sessionStorage  | Tab                | Session             | Temporary dismiss  |
| Cookie          | Domain             | Configurable        | Cross-subdomain    |
| Backend         | User account       | Permanent           | Logged-in users    |

#### Specification

| Property          | Type              | Default       | Description                |
|-------------------|-------------------|---------------|----------------------------|
| storageKey        | String            | "tour:{id}"   | Unique storage key         |
| storageType       | StorageType       | localStorage  | Where to persist           |
| expiryDays        | Maybe Int         | Nothing       | Auto-reset after N days    |
| respectGlobal     | Boolean           | true          | Honor global "no tours"    |

────────────────────────────────────────────────────────────────────────────────

## 4. Timing and Pacing

### 4.1 Auto-Advance

Automatic progression through steps.

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| autoAdvance     | Boolean           | false      | Enable auto-progression        |
| advanceDelay    | Milliseconds      | 5000       | Time before advancing          |
| showCountdown   | Boolean           | true       | Display remaining time         |
| pauseOnHover    | Boolean           | true       | Stop timer on mouse hover      |
| pauseOnFocus    | Boolean           | true       | Stop timer on keyboard focus   |
| cancelOnInteract| Boolean           | true       | User click stops auto-advance  |

#### Countdown Visualization

```
Progress bar depletes: ████████░░ (fading right to left)
Or circular: ◔ → ◑ → ◕ → ● (radial wipe)
```

### 4.2 Wait For User Action

Action-gated progression for interactive tutorials.

#### Wait Condition Types

| Type            | Trigger                         | Use Case                   |
|-----------------|---------------------------------|----------------------------|
| click           | User clicks target element      | Button tutorials           |
| input           | User types in field             | Form tutorials             |
| change          | Form value changes              | Dropdown/checkbox          |
| scroll          | User scrolls to element         | Content discovery          |
| custom          | Arbitrary state predicate       | Complex conditions         |
| timeout         | Fallback after N seconds        | Prevent stuck states       |

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| waitFor         | WaitCondition     | click      | Condition to advance           |
| waitTarget      | Maybe Selector    | Nothing    | Element to monitor (if != step target) |
| waitTimeout     | Maybe Ms          | Nothing    | Fallback timeout               |
| showHint        | Boolean           | true       | Show hint after delay          |
| hintDelay       | Milliseconds      | 3000       | Time before showing hint       |

### 4.3 Pause on Hover

Tooltip interaction pauses timers.

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| pauseOnHover    | Boolean           | true       | Pause on mouse enter           |
| resumeDelay     | Milliseconds      | 500        | Delay before resuming on leave |
| pauseOnFocus    | Boolean           | true       | Pause when tooltip focused     |

### 4.4 Speed Controls

User control over tour pacing.

#### Options

| Control         | Implementation                  | Accessibility              |
|-----------------|---------------------------------|----------------------------|
| Pause/Play      | Toggle button in tooltip        | Required for auto-advance  |
| Speed selector  | 0.5x, 1x, 1.5x, 2x              | Optional                   |
| Skip section    | Jump to next major section      | Useful for long tours      |
| Restart         | Return to step 1                | Always provide             |

────────────────────────────────────────────────────────────────────────────────

## 5. Responsive Behaviors

### 5.1 Repositioning on Resize

#### Specification

| Property        | Type              | Default    | Description                    |
|-----------------|-------------------|------------|--------------------------------|
| updateOnResize  | Boolean           | true       | Reposition on window resize    |
| resizeDebounce  | Milliseconds      | 100        | Debounce resize events         |
| recalcBounds    | Boolean           | true       | Recalculate target bounds      |

#### Implementation

```javascript
// ResizeObserver for target element changes
// Window resize listener (debounced) for viewport changes
// Floating UI autoUpdate() handles both
```

### 5.2 Mobile vs Desktop

#### Breakpoint Configuration

| Breakpoint  | Width         | Tooltip Style           | Navigation           |
|-------------|---------------|-------------------------|----------------------|
| mobile      | < 640px       | Bottom sheet            | Swipe gestures       |
| tablet      | 640-1024px    | Floating, larger        | Touch + keyboard     |
| desktop     | > 1024px      | Floating, standard      | Mouse + keyboard     |

#### Mobile-Specific Adjustments

| Adjustment              | Specification                              |
|-------------------------|--------------------------------------------|
| Tooltip position        | Bottom sheet (fixed bottom) preferred      |
| Tap targets             | Minimum 44x44px (WCAG 2.5.5)               |
| Button spacing          | Minimum 8px between interactive elements   |
| Font size               | Minimum 16px to prevent iOS zoom           |
| Virtual keyboard        | Reposition when keyboard opens             |

### 5.3 Graceful Degradation

When target elements are missing or not visible.

#### Fallback Strategies

| Scenario                | Fallback                                   |
|-------------------------|--------------------------------------------|
| Target not found        | Skip step, log warning, continue           |
| Target not visible      | Scroll into view, then show                |
| Target too small        | Use parent element or skip                 |
| Multiple matches        | Use first match, log warning               |
| Async target            | Wait with timeout, then skip               |

#### Target Visibility Detection

| Check                   | Method                                     |
|-------------------------|--------------------------------------------|
| In DOM                  | querySelector returns element              |
| Displayed               | offsetParent !== null (or position check)  |
| Visible                 | getBoundingClientRect().width > 0          |
| In viewport             | IntersectionObserver entry.isIntersecting  |
| Not obscured            | elementFromPoint (expensive, optional)     |

────────────────────────────────────────────────────────────────────────────────
                                                              // PRIORITY MATRIX
────────────────────────────────────────────────────────────────────────────────

## Feature Priority Matrix

| Feature                    | Priority | Complexity | Impact | MVP |
|----------------------------|----------|------------|--------|-----|
| Spotlight overlay          | P0       | Medium     | High   | Yes |
| Basic tooltip positioning  | P0       | Medium     | High   | Yes |
| Keyboard navigation        | P0       | Low        | High   | Yes |
| Step progression           | P0       | Low        | High   | Yes |
| Focus management           | P0       | Medium     | High   | Yes |
| Progress indicator (dots)  | P1       | Low        | Medium | Yes |
| Spring animations          | P1       | Medium     | Medium | No  |
| Auto-positioning (flip)    | P1       | Medium     | High   | Yes |
| Mobile responsive          | P1       | Medium     | High   | Yes |
| Morph transitions          | P2       | High       | Medium | No  |
| Wait for action            | P2       | Medium     | Medium | No  |
| Branching paths            | P2       | High       | Low    | No  |
| Auto-advance               | P2       | Low        | Low    | No  |
| Multiple highlights        | P3       | High       | Low    | No  |
| Gesture support            | P3       | Medium     | Low    | No  |
| Speed controls             | P3       | Low        | Low    | No  |

────────────────────────────────────────────────────────────────────────────────
                                                      // ACCESSIBILITY CHECKLIST
────────────────────────────────────────────────────────────────────────────────

## WCAG 2.1 AA Compliance Checklist

### Perceivable

- [ ] Color contrast ratio >= 4.5:1 for text
- [ ] Color contrast ratio >= 3:1 for UI components
- [ ] Information not conveyed by color alone
- [ ] Text resizable to 200% without loss
- [ ] Content reflows at 320px width

### Operable

- [ ] All functionality keyboard accessible
- [ ] No keyboard traps
- [ ] Focus visible (2px outline minimum)
- [ ] Focus order logical
- [ ] Skip mechanism provided (Escape to dismiss)
- [ ] Pointer gestures have keyboard alternatives
- [ ] Target size >= 44x44px on touch devices
- [ ] Motion can be disabled (prefers-reduced-motion)

### Understandable

- [ ] Language identified in markup
- [ ] Focus doesn't trigger context change
- [ ] Consistent navigation patterns
- [ ] Error identification and suggestions

### Robust

- [ ] Valid HTML/ARIA
- [ ] Name, role, value exposed to AT
- [ ] Status messages announced (aria-live)

────────────────────────────────────────────────────────────────────────────────

────────────────────────────────────────────────────────────────────────────────
                                                                       // ROUND 2
                                                         // API & TYPE DESIGN //
────────────────────────────────────────────────────────────────────────────────

## 6. API Design Patterns from Leading Libraries

### 6.1 Library Architecture Comparison

| Library       | Architecture Pattern     | State Model           | Step Config        |
|---------------|--------------------------|----------------------|-------------------|
| Shepherd.js   | OOP + Event Emitter      | Mutable Tour/Step    | Object options    |
| React Joyride | Controlled/Uncontrolled  | React state + callback | Array of steps   |
| Driver.js     | Functional Factory       | Internal + getState() | Config object    |

### 6.2 Shepherd.js API Analysis

**Tour Configuration:**
```typescript
interface TourOptions {
  classPrefix?: string;               // CSS namespace
  confirmCancel?: boolean | Function; // Async cancel confirmation
  confirmCancelMessage?: string;      // Dialog message
  defaultStepOptions?: StepOptions;   // Shared step defaults
  exitOnEsc?: boolean;                // Default: true
  keyboardNavigation?: boolean;       // Arrow key nav, default: true
  modalContainer?: HTMLElement;       // Modal mount point
  stepsContainer?: HTMLElement;       // Steps mount point
  tourName?: string;                  // ID suffix
  useModalOverlay?: boolean;          // Spotlight overlay
  steps?: StepOptions[];              // Initial steps
}
```

**Step Configuration:**
```typescript
interface StepOptions {
  id?: string;                        // Unique step identifier
  title?: string;                     // Step heading (h3)
  text?: string | HTMLElement;        // Body content
  attachTo?: {
    element: string | HTMLElement | (() => HTMLElement);
    on?: Placement;                   // Floating UI placement
  };
  advanceOn?: {                       // Auto-advance trigger
    selector: string;
    event: string;                    // Any DOM event
  };
  arrow?: boolean | ArrowOptions;
  beforeShowPromise?: () => Promise<void>;
  buttons?: ButtonOptions[];
  canClickTarget?: boolean;           // Allow target interaction
  classes?: string;
  extraHighlights?: string[];         // Additional highlighted elements
  floatingUIOptions?: FloatingUIConfig;
  highlightClass?: string;            // Class for target element
  scrollTo?: boolean | ScrollOptions;
  scrollToHandler?: () => void;
  showOn?: () => boolean;             // Conditional display
  when?: {                            // Lifecycle hooks
    show?: () => void;
    hide?: () => void;
    destroy?: () => void;
    cancel?: () => void;
    complete?: () => void;
  };
}
```

**Key Insight**: Shepherd uses lazy evaluation for `attachTo.element` via function,
enabling async/dynamic element resolution.

### 6.3 React Joyride State Pattern

**Controlled Mode:**
```typescript
// External state management (Redux/Context)
const [stepIndex, setStepIndex] = useState(0);

<Joyride
  stepIndex={stepIndex}  // Makes it "controlled"
  callback={(data) => {
    const { action, index, type, status } = data;
    
    if ([STATUS.FINISHED, STATUS.SKIPPED].includes(status)) {
      // Tour ended
    } else if (type === EVENTS.STEP_AFTER) {
      // Advance step
      setStepIndex(index + (action === ACTIONS.PREV ? -1 : 1));
    }
  }}
/>
```

**Callback Data Structure:**
```typescript
interface CallbackData {
  action: 'start' | 'next' | 'prev' | 'close' | 'skip' | 'reset';
  index: number;           // Current step index
  type: EventType;         // EVENTS enum
  status: StatusType;      // STATUS enum
  step: Step;              // Current step config
  size: number;            // Total steps
  lifecycle: Lifecycle;    // Step lifecycle phase
}
```

**Key Insight**: React Joyride separates "controlled" (external state) from 
"uncontrolled" (internal state) modes via the `stepIndex` prop.

### 6.4 Driver.js Functional Pattern

**API Methods:**
```typescript
const driverObj = driver(config);

// Navigation
driverObj.drive();              // Start at step 0
driverObj.drive(4);             // Start at step 4
driverObj.moveNext();
driverObj.movePrevious();
driverObj.moveTo(4);

// State queries
driverObj.hasNextStep(): boolean;
driverObj.hasPreviousStep(): boolean;
driverObj.isFirstStep(): boolean;
driverObj.isLastStep(): boolean;
driverObj.getActiveIndex(): number;
driverObj.getActiveStep(): DriveStep;
driverObj.getPreviousStep(): DriveStep;
driverObj.getActiveElement(): HTMLElement;
driverObj.getState(): State;

// Lifecycle
driverObj.setSteps([...]);
driverObj.highlight({...});     // Single element
driverObj.destroy();
```

**Hooks System:**
```typescript
interface DriveStep {
  element?: string;
  popover?: PopoverConfig;
  
  // Per-step hooks (override driver-level)
  onHighlightStarted?: (element, step, options) => void;
  onHighlighted?: (element, step, options) => void;
  onDeselected?: (element, step, options) => void;
  
  // Navigation override
  onNextClick?: (element, step, options) => void;  // Return to prevent default
  onPrevClick?: (element, step, options) => void;
  onCloseClick?: (element, step, options) => void;
}
```

**Key Insight**: Driver.js uses hook callbacks for async control—`onNextClick`
can prevent default and call `moveNext()` after async operations complete.

────────────────────────────────────────────────────────────────────────────────

## 7. PureScript Type Design for Hydrogen

### 7.1 The Elm Architecture for Tours

Following Hydrogen's `State × Msg → State × [Cmd]` pattern, tours are modeled
as a finite state machine where the update function handles all transitions.

```purescript
-- TEA enforces that all state changes go through update
-- The model contains the entire state (single source of truth)
-- Commands are effects that return messages
-- The view is a pure function of state
```

### 7.2 Core Type Definitions

#### Tour Identifier (Type-Safe IDs)

```purescript
-- Phantom type for tour identity
newtype TourId (name :: Symbol) = TourId UUID

-- Smart constructor ensures UUID5 determinism
mkTourId :: forall name. IsSymbol name => Proxy name -> TourId name
mkTourId _ = TourId (uuid5 tourNamespace (reflectSymbol (Proxy :: Proxy name)))

-- Step identifiers scoped to their tour
newtype StepId (tour :: Symbol) (step :: Symbol) = StepId UUID
```

#### Target Selection

```purescript
-- Bounded target specification (no raw strings)
data Target
  = BySelector Selector                    -- CSS selector (validated)
  | ByTestId TestId                        -- data-testid attribute
  | ByRole AriaRole (Maybe AccessibleName) -- ARIA role + optional name
  | ByElement ElementRef                   -- Direct element reference
  | NoTarget                               -- Centered modal (no attachment)
  | DeferredTarget (Effect (Maybe Target)) -- Lazy/async resolution

-- Validated CSS selector
newtype Selector = Selector String
derive instance newtypeSelector :: Newtype Selector _

mkSelector :: String -> Either SelectorError Selector
-- Parses and validates CSS selector syntax

-- ARIA roles (bounded enumeration)
data AriaRole
  = RoleButton | RoleLink | RoleTextbox | RoleCheckbox
  | RoleDialog | RoleNavigation | RoleMain | RoleForm
  -- ... complete ARIA role set
```

#### Placement (Following Floating UI)

```purescript
data Side = Top | Right | Bottom | Left

data Alignment = Start | Center | End

type Placement = { side :: Side, align :: Alignment }

-- Placement with fallback chain
type PlacementConfig =
  { preferred :: Placement
  , fallbacks :: Array Placement  -- Flip alternatives
  , padding   :: Pixel            -- Viewport padding
  , offset    :: { main :: Pixel, cross :: Pixel }
  }
```

#### Step Content

```purescript
-- Step content is Element, not strings
data StepContent msg
  = SimpleContent
      { title :: Maybe (Element msg)
      , body  :: Element msg
      }
  | CustomContent (Element msg)

-- Button configuration
data ButtonAction msg
  = Next                          -- Advance to next step
  | Previous                      -- Go to previous step
  | Skip                          -- Skip tour
  | Complete                      -- Complete tour (from any step)
  | GoTo (StepId tour step)       -- Jump to specific step
  | Custom msg                    -- Emit custom message

type Button msg =
  { label   :: Element msg        -- Button content
  , action  :: ButtonAction msg
  , variant :: ButtonVariant      -- Primary | Secondary | Text
  , disabled :: Boolean
  }

data ButtonVariant = Primary | Secondary | Text
```

#### Step Definition

```purescript
type Step tour step msg =
  { id          :: StepId tour step
  , target      :: Target
  , content     :: StepContent msg
  , placement   :: PlacementConfig
  , buttons     :: Array (Button msg)
  , arrow       :: Boolean
  , highlight   :: HighlightConfig
  , waitFor     :: Maybe WaitCondition
  , showIf      :: State -> Boolean       -- Conditional display
  , beforeShow  :: Maybe (Aff Unit)       -- Async pre-show hook
  , onShow      :: Maybe msg              -- Message on show
  , onHide      :: Maybe msg              -- Message on hide
  }

type HighlightConfig =
  { padding     :: Pixel
  , borderRadius :: Pixel
  , extraTargets :: Array Target          -- Additional highlights
  }

data WaitCondition
  = WaitForClick Target
  | WaitForInput Target
  | WaitForScroll Target
  | WaitForEvent String Target            -- Custom DOM event
  | WaitForPredicate (State -> Boolean)
  | WaitForTimeout Milliseconds
  | WaitForAll (Array WaitCondition)
  | WaitForAny (Array WaitCondition)
```

### 7.3 Tour State Machine

```purescript
-- Tour lifecycle states
data TourPhase
  = TourInactive                          -- Not started
  | TourActive Int                        -- Active at step index
  | TourPaused Int                        -- Paused (e.g., waiting)
  | TourCompleted                         -- User finished all steps
  | TourSkipped Int                       -- User skipped at step N
  | TourDismissed Int                     -- User dismissed at step N

-- Complete tour state
type TourState tour =
  { phase       :: TourPhase
  , steps       :: Array (Step tour _ _)  -- Existential step types
  , stepHistory :: Array Int              -- Visited step indices
  , startTime   :: Maybe Instant          -- When tour started
  , analytics   :: TourAnalytics          -- Accumulated metrics
  }

type TourAnalytics =
  { stepTimes   :: Map Int Milliseconds   -- Time spent on each step
  , interactions :: Array Interaction     -- User interactions
  , dropOffStep :: Maybe Int              -- Where user exited (if not completed)
  }

data Interaction
  = ButtonClicked String Int Instant      -- Button label, step, time
  | TargetClicked Int Instant             -- Step, time
  | KeyPressed Key Int Instant            -- Key, step, time
  | Snoozed Int Instant                   -- Step, time
```

### 7.4 Tour Messages (Msg Type)

```purescript
-- All possible tour events
data TourMsg tour
  -- Lifecycle
  = StartTour
  | PauseTour
  | ResumeTour
  | SkipTour
  | CompleteTour
  | DismissTour
  
  -- Navigation
  | NextStep
  | PreviousStep
  | GoToStep Int
  | Restart
  
  -- Timing
  | AutoAdvance                           -- Timer triggered
  | SnoozeTour Milliseconds               -- Defer tour
  
  -- Target resolution
  | TargetFound Int Target                -- Step index, resolved target
  | TargetNotFound Int                    -- Step index
  | TargetScrolled Int                    -- Target scrolled into view
  
  -- Wait conditions
  | WaitConditionMet Int                  -- Step index
  | WaitTimeout Int                       -- Step index
  
  -- Analytics
  | RecordInteraction Interaction
  | EmitAnalytics TourAnalytics
```

### 7.5 Update Function

```purescript
update :: forall tour msg. TourMsg tour -> TourState tour -> Tuple (TourState tour) (Array (Cmd (TourMsg tour)))

update msg state = case msg of
  StartTour ->
    if canStart state
    then Tuple (state { phase = TourActive 0, startTime = Just now })
               [ scrollToStep 0
               , emitEvent TourStarted
               ]
    else Tuple state []
  
  NextStep ->
    case state.phase of
      TourActive idx ->
        let nextIdx = idx + 1
        in if nextIdx < length state.steps
           then Tuple (advanceToStep nextIdx state)
                      [ recordStepTime idx
                      , scrollToStep nextIdx
                      ]
           else update CompleteTour state
      _ -> Tuple state []
  
  GoToStep idx ->
    case state.phase of
      TourActive _ | validStepIndex idx state ->
        Tuple (advanceToStep idx state)
              [ scrollToStep idx ]
      _ -> Tuple state []
  
  CompleteTour ->
    Tuple (state { phase = TourCompleted })
          [ emitAnalytics state.analytics
          , persistCompletion (tourId state)
          , focusRestoration
          ]
  
  TargetNotFound idx ->
    -- Graceful degradation: skip step, log warning
    let nextIdx = idx + 1
    in if nextIdx < length state.steps
       then update (GoToStep nextIdx) state
       else update CompleteTour state
  
  _ -> Tuple state []
```

### 7.6 View Function

```purescript
view :: forall tour msg. TourState tour -> Element msg
view state = case state.phase of
  TourInactive -> empty
  
  TourActive idx ->
    let step = state.steps !! idx
    in tourOverlay
         [ spotlight step.target step.highlight
         , tooltip
             { placement: step.placement
             , content: step.content
             , buttons: step.buttons
             , progress: { current: idx + 1, total: length state.steps }
             , arrow: step.arrow
             }
         ]
  
  TourPaused _ ->
    -- Could show "paused" indicator
    empty
  
  _ -> empty
```

────────────────────────────────────────────────────────────────────────────────
                                                       // CONTENT & UX PATTERNS
────────────────────────────────────────────────────────────────────────────────

## 8. Content Best Practices

### 8.1 Core UX Writing Principles

| Principle     | Description                                      | Application              |
|---------------|--------------------------------------------------|--------------------------|
| Clarity       | User understands on first read                   | No jargon, simple words  |
| Conciseness   | Minimal words, maximum meaning                   | Every word earns its place|
| Consistency   | Same terms, tone, formatting                     | Build familiarity/trust  |
| Usability     | Helps user complete task                         | Action-oriented          |
| Context       | Right message at right moment                    | Adapt to user state      |

### 8.2 Step Content Guidelines

#### Title Guidelines

| Rule                      | Good Example                    | Bad Example                      |
|---------------------------|---------------------------------|----------------------------------|
| Action-oriented           | "Create your first project"     | "Projects"                       |
| Benefit-focused           | "Find answers instantly"        | "Search functionality"           |
| Concise (3-5 words)       | "Share with your team"          | "How to share documents with team members" |
| No periods                | "Set up notifications"          | "Set up notifications."          |
| Sentence case             | "Manage your settings"          | "Manage Your Settings"           |

#### Body Copy Guidelines

| Rule                      | Good Example                    | Bad Example                      |
|---------------------------|---------------------------------|----------------------------------|
| One idea per step         | "Click here to add a task"      | "Click here to add a task, or press T, or use the menu..." |
| Max 2-3 sentences         | 40-60 words                     | 100+ words                       |
| Active voice              | "Select a template"             | "A template should be selected"  |
| User-focused ("you")      | "You can organize..."           | "Users can organize..."          |
| No technical jargon       | "Your dashboard"                | "The UI viewport"                |

#### Character Limits (Recommended)

| Element        | Min  | Optimal | Max  | Notes                           |
|----------------|------|---------|------|---------------------------------|
| Title          | 15   | 25      | 40   | Single line preferred           |
| Body           | 50   | 80      | 120  | 2-3 sentences                   |
| Button label   | 4    | 8       | 20   | Action verb + object            |
| Progress text  | 5    | 12      | 20   | "Step 2 of 5"                   |

### 8.3 Button Label Patterns

| Action          | Primary Button    | Secondary Button | Notes                    |
|-----------------|-------------------|------------------|--------------------------|
| Next step       | "Next", "Continue"| "Skip"           | Never "OK"               |
| Last step       | "Get started", "Done" | "Back"       | Celebrate completion     |
| Optional step   | "Got it"          | "Skip for now"   | Low pressure             |
| Interactive     | "Try it"          | "I'll do it later"| Encourage action        |

### 8.4 Tone Variations by Context

| User State        | Tone              | Example                              |
|-------------------|-------------------|--------------------------------------|
| First-time user   | Warm, encouraging | "Welcome! Let's get you set up."     |
| Learning feature  | Helpful, clear    | "Here's how to create reports."      |
| Complex task      | Patient, detailed | "This takes a few steps. Let's start."|
| Error recovery    | Reassuring        | "No worries—let's try again."        |
| Power user tip    | Efficient, direct | "Pro tip: Press ⌘K for quick access."|

### 8.5 Progressive Disclosure Patterns

```
Level 1: Essential (Always shown)
├── What is this feature?
├── How do I use it?
└── What's my next step?

Level 2: Helpful (Show if user hesitates)
├── Why should I use this?
├── What are common use cases?
└── Where can I learn more?

Level 3: Advanced (On-demand only)
├── Keyboard shortcuts
├── Advanced options
└── Integration details
```

#### Implementation

| Indicator        | Trigger                | Content Type              |
|------------------|------------------------|---------------------------|
| Hint after 3s    | User hasn't acted      | Clarifying instruction    |
| "Learn more" link| User clicks            | Extended explanation      |
| Tooltip on hover | User explores          | Quick reference           |
| Help icon        | Always visible         | Full documentation        |

### 8.6 Anti-Patterns to Avoid

| Anti-Pattern              | Problem                          | Solution                    |
|---------------------------|----------------------------------|-----------------------------|
| Wall of text              | Overwhelms, user won't read      | 2-3 sentences max           |
| Forced linear tour        | Ignores user intent              | Allow skip, snooze          |
| Marketing speak           | Breaks trust in product context  | Focus on action, not sell   |
| Unclear next action       | User doesn't know what to do     | Explicit CTA                |
| Too many steps            | Fatigue, drop-off                | Max 5-7 steps per tour      |
| Technical jargon          | Confuses non-experts             | Plain language              |
| Inconsistent terminology  | Creates cognitive load           | Use style guide             |
| Interruptive timing       | Annoys user mid-task             | Contextual triggers         |

────────────────────────────────────────────────────────────────────────────────
                                                       // ANALYTICS & TRACKING
────────────────────────────────────────────────────────────────────────────────

## 9. Analytics Design

### 9.1 Core Metrics

| Metric              | Definition                           | Target Range    | Action if Low           |
|---------------------|--------------------------------------|-----------------|-------------------------|
| Completion Rate     | % who finish all steps               | 30-70%          | Shorten tour, improve content |
| Drop-off Rate       | % who exit at each step              | < 20% per step  | Fix specific step       |
| Snooze Rate         | % who postpone                       | 10-25%          | Improve timing/targeting|
| Time per Step       | Seconds spent on each step           | 5-15s           | Too long = confusing    |
| Goal Completion     | % who achieve tour's objective       | Varies          | Measure business impact |
| Return Rate         | % who come back after snooze         | 15-25%          | Good snooze UX          |

### 9.2 Industry Benchmarks (Intercom Data)

| Tour Length | Median Completion | Step 2 Retention | Step 3 Retention |
|-------------|-------------------|------------------|------------------|
| 2 steps     | 55%               | 72%              | N/A              |
| 3 steps     | 45%               | 68%              | 58%              |
| 4 steps     | 40%               | 65%              | 55%              |
| 5 steps     | 34%               | 62%              | 52%              |

**Key Findings:**
- Post messages have 14% higher engagement on first step vs. tooltips
- Contextually-triggered tours: 69.56% completion (well above average)
- Snooze option: 20% of users return to complete

### 9.3 Event Schema Design

#### Event Naming Convention

```
tour.<action>.<detail>
```

#### Core Events

| Event Name              | Payload                                | When Fired                |
|-------------------------|----------------------------------------|---------------------------|
| tour.started            | {tourId, trigger, userId, timestamp}   | First step shown          |
| tour.step.viewed        | {tourId, stepIndex, stepId, timestamp} | Step becomes visible      |
| tour.step.completed     | {tourId, stepIndex, durationMs}        | User advances from step   |
| tour.step.skipped       | {tourId, stepIndex}                    | User skips specific step  |
| tour.completed          | {tourId, totalDurationMs, stepsViewed} | Last step finished        |
| tour.dismissed          | {tourId, stepIndex, reason}            | User exits early          |
| tour.snoozed            | {tourId, stepIndex, snoozeDurationMs}  | User postpones            |
| tour.resumed            | {tourId, stepIndex}                    | User returns from snooze  |
| tour.target_not_found   | {tourId, stepIndex, selector}          | Target element missing    |
| tour.button.clicked     | {tourId, stepIndex, buttonLabel}       | Button interaction        |
| tour.goal.completed     | {tourId, goalId, stepIndex}            | Conversion goal achieved  |

#### Event Payload Types

```purescript
type TourEvent =
  { eventName  :: EventName
  , tourId     :: TourId
  , userId     :: Maybe UserId           -- Anonymous or identified
  , sessionId  :: SessionId
  , timestamp  :: Instant
  , payload    :: EventPayload
  , context    :: EventContext
  }

type EventContext =
  { pageUrl    :: URL
  , viewport   :: { width :: Int, height :: Int }
  , device     :: DeviceType              -- Desktop | Tablet | Mobile
  , locale     :: Locale
  , tourVersion :: Version                -- For A/B testing
  }

data EventPayload
  = StepPayload { stepIndex :: Int, stepId :: StepId, durationMs :: Maybe Int }
  | ButtonPayload { stepIndex :: Int, buttonLabel :: String }
  | DismissPayload { stepIndex :: Int, reason :: DismissReason }
  | GoalPayload { goalId :: GoalId, stepIndex :: Int }
  | ErrorPayload { stepIndex :: Int, errorType :: String, details :: String }

data DismissReason
  = ClickedClose
  | PressedEscape
  | ClickedOutside
  | NavigatedAway
  | Timeout
```

### 9.4 Funnel Analysis

```
Start Tour (100%)
    │
    ├─── Drop: 15% (didn't engage)
    │
    ▼
Step 1 (85%)
    │
    ├─── Drop: 12%
    │
    ▼
Step 2 (73%)
    │
    ├─── Drop: 8%
    │
    ▼
Step 3 (65%)
    │
    ├─── Drop: 10%
    │
    ▼
Step 4 (55%)
    │
    ├─── Drop: 15%
    │
    ▼
Step 5 (40%) ← Completion
```

**Analysis Triggers:**
- Drop > 20% at any step → Review that step's content/targeting
- Consistent decline → Tour too long
- Spike at specific step → Content issue or broken target

### 9.5 A/B Testing Framework

```purescript
type Experiment =
  { experimentId :: ExperimentId
  , name         :: String
  , variants     :: NonEmptyArray Variant
  , allocation   :: AllocationStrategy
  , metrics      :: Array MetricConfig
  , status       :: ExperimentStatus
  }

data Variant = Variant
  { variantId    :: VariantId
  , name         :: String
  , tourConfig   :: TourConfig
  , allocation   :: Percentage            -- 0-100, sum must = 100
  }

data AllocationStrategy
  = Random                                -- Pure random
  | UserIdHash                            -- Consistent per user
  | SegmentBased (Array Segment)          -- Different allocation by segment

type MetricConfig =
  { metricId     :: MetricId
  , name         :: String
  , eventName    :: EventName
  , aggregation  :: Aggregation           -- Count | Sum | Average | Percentage
  , direction    :: Direction             -- Higher | Lower is better
  }
```

### 9.6 Privacy & Compliance

| Requirement        | Implementation                           | GDPR/CCPA          |
|--------------------|------------------------------------------|-------------------|
| Consent            | Check consent before tracking            | Required          |
| Data minimization  | Only collect necessary events            | Required          |
| Anonymization      | Hash user IDs, no PII in events          | Best practice     |
| Retention          | Auto-delete after 90 days                | Configurable      |
| Right to delete    | Support user data deletion               | Required          |
| Opt-out            | Honor DNT / analytics opt-out            | Best practice     |

```purescript
-- Privacy-aware event emission
emitEvent :: TourEvent -> Effect Unit
emitEvent event = do
  consent <- getAnalyticsConsent
  when consent $ do
    anonymized <- anonymizeEvent event
    sendToAnalytics anonymized

anonymizeEvent :: TourEvent -> Effect TourEvent
anonymizeEvent event = do
  hashedUserId <- hash event.userId
  pure $ event { userId = hashedUserId }
```

### 9.7 Dashboard Metrics Summary

| Section            | Metrics                                  | Visualization       |
|--------------------|------------------------------------------|---------------------|
| Overview           | Total views, completion rate, avg duration | KPI cards          |
| Funnel             | Step-by-step retention                   | Funnel chart        |
| Drop-off           | Per-step drop-off rates                  | Bar chart           |
| Time Analysis      | Time per step distribution               | Box plot            |
| Trends             | Completion over time                     | Line chart          |
| Segments           | Completion by user segment               | Grouped bar         |
| A/B Results        | Variant performance comparison           | Table + significance|

────────────────────────────────────────────────────────────────────────────────
                                                              // IMPLEMENTATION
                                                                 // PRIORITIES
────────────────────────────────────────────────────────────────────────────────

## 10. Implementation Roadmap

### Phase 1: Core Infrastructure (MVP)

| Component                | Priority | Complexity | Dependencies    |
|--------------------------|----------|------------|-----------------|
| TourState ADT            | P0       | Medium     | None            |
| TourMsg ADT              | P0       | Low        | None            |
| Update function          | P0       | High       | State, Msg      |
| Step configuration types | P0       | Medium     | None            |
| Target resolution        | P0       | Medium     | DOM FFI         |
| Spotlight overlay        | P0       | Medium     | Canvas/SVG      |
| Basic tooltip            | P0       | Medium     | Floating UI     |
| Keyboard navigation      | P0       | Low        | None            |
| Focus management         | P0       | Medium     | DOM FFI         |

### Phase 2: Enhanced UX

| Component                | Priority | Complexity | Dependencies    |
|--------------------------|----------|------------|-----------------|
| Progress indicator       | P1       | Low        | Phase 1         |
| Spring animations        | P1       | Medium     | Animation lib   |
| Auto-positioning (flip)  | P1       | Medium     | Phase 1         |
| Mobile responsive        | P1       | Medium     | Phase 1         |
| Scroll following         | P1       | Medium     | Phase 1         |
| Arrow animations         | P1       | Low        | Phase 1         |

### Phase 3: Advanced Features

| Component                | Priority | Complexity | Dependencies    |
|--------------------------|----------|------------|-----------------|
| Wait conditions          | P2       | High       | Phase 1         |
| Morph transitions        | P2       | High       | Animation lib   |
| Analytics integration    | P2       | Medium     | Event system    |
| A/B testing              | P2       | High       | Analytics       |
| Branching paths          | P2       | High       | Phase 1         |
| Persistence (storage)    | P2       | Low        | LocalStorage FFI|

### Phase 4: Polish

| Component                | Priority | Complexity | Dependencies    |
|--------------------------|----------|------------|-----------------|
| Multiple highlights      | P3       | High       | Phase 1         |
| Gesture support          | P3       | Medium     | Mobile phase    |
| Speed controls           | P3       | Low        | Auto-advance    |
| Rich content (video)     | P3       | Medium     | Phase 1         |
| Accessibility audit      | P3       | Medium     | All phases      |

────────────────────────────────────────────────────────────────────────────────
                                                                       — Opus 4.5
                                                                      2026-02-24
────────────────────────────────────────────────────────────────────────────────
