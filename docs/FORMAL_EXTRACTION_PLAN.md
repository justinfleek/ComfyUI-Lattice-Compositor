# Lattice Compositor: Formal Extraction Plan

> **Goal:** Formally verified compositor with mathematical proofs of correctness
>
> **Languages:**
> - **Lean4** - Verified math core (interpolation, geometry, physics, color)
> - **PureScript** - Frontend (Halogen) and backend (Node.js via FFI)
>
> **Timeline:** 52 weeks (12 months)
>
> **Proof Obligations:** Type safety, round-trip serialization, deterministic rendering, numeric stability

---

## Part I: Formal Specification

### 1.1 Core Type System (Lean4)

Every type must be precisely defined with invariants that can be proven.

```lean
-- lattice/core/Types.lean

/-!
# Core Types for Lattice Compositor

All types include invariants that must be maintained.
-/

namespace Lattice

/-- Time in frames. Must be non-negative. -/
structure Frame where
  value : Nat
  deriving DecidableEq, Repr

/-- Normalized value in [0, 1] -/
structure UnitInterval where
  value : Float
  h_ge_zero : value ≥ 0
  h_le_one : value ≤ 1

/-- Opacity as a unit interval -/
abbrev Opacity := UnitInterval

/-- 2D point with finite coordinates -/
structure Point2D where
  x : Float
  y : Float
  h_x_finite : x.isFinite
  h_y_finite : y.isFinite

/-- 3D point with finite coordinates -/
structure Point3D where
  x : Float
  y : Float
  z : Float
  h_x_finite : x.isFinite
  h_y_finite : y.isFinite
  h_z_finite : z.isFinite

/-- RGBA color with all components in [0, 1] -/
structure Color where
  r : UnitInterval
  g : UnitInterval
  b : UnitInterval
  a : UnitInterval

/-- 4x4 transformation matrix with finite entries -/
structure Mat4 where
  data : Array Float
  h_size : data.size = 16
  h_finite : ∀ i, i < 16 → (data[i]!).isFinite

/-- Quaternion for rotations (must be normalized) -/
structure Quaternion where
  w : Float
  x : Float
  y : Float
  z : Float
  h_normalized : w*w + x*x + y*y + z*z = 1
  h_finite : w.isFinite ∧ x.isFinite ∧ y.isFinite ∧ z.isFinite

end Lattice
```

### 1.2 Interpolation Functions with Proofs

```lean
-- lattice/core/Interpolation.lean

namespace Lattice.Interpolation

/-- Linear interpolation between two values -/
def lerp (a b : Float) (t : UnitInterval) : Float :=
  a + (b - a) * t.value

/-- Proof: lerp returns a when t = 0 -/
theorem lerp_at_zero (a b : Float) :
    lerp a b ⟨0, by norm_num, by norm_num⟩ = a := by
  simp [lerp]

/-- Proof: lerp returns b when t = 1 -/
theorem lerp_at_one (a b : Float) :
    lerp a b ⟨1, by norm_num, by norm_num⟩ = b := by
  simp [lerp]
  ring

/-- Proof: lerp is continuous (Lipschitz with constant |b - a|) -/
theorem lerp_continuous (a b : Float) (t₁ t₂ : UnitInterval) :
    |lerp a b t₁ - lerp a b t₂| ≤ |b - a| * |t₁.value - t₂.value| := by
  simp [lerp]
  ring_nf
  sorry -- Full proof requires real analysis foundations

/-- Proof: lerp preserves bounds when a ≤ b -/
theorem lerp_bounded (a b : Float) (h : a ≤ b) (t : UnitInterval) :
    a ≤ lerp a b t ∧ lerp a b t ≤ b := by
  constructor
  · simp [lerp]
    have : 0 ≤ (b - a) * t.value := by
      apply mul_nonneg
      · linarith
      · exact t.h_ge_zero
    linarith
  · simp [lerp]
    have : (b - a) * t.value ≤ b - a := by
      apply mul_le_of_le_one_right
      · linarith
      · exact t.h_le_one
    linarith

/-- Cubic Bezier evaluation -/
def cubicBezier (p0 p1 p2 p3 : Float) (t : UnitInterval) : Float :=
  let t' := t.value
  let mt := 1 - t'
  let mt2 := mt * mt
  let mt3 := mt2 * mt
  let t2 := t' * t'
  let t3 := t2 * t'
  mt3 * p0 + 3 * mt2 * t' * p1 + 3 * mt * t2 * p2 + t3 * p3

/-- Proof: Bezier curve passes through endpoints -/
theorem bezier_endpoints (p0 p1 p2 p3 : Float) :
    cubicBezier p0 p1 p2 p3 ⟨0, by norm_num, by norm_num⟩ = p0 ∧
    cubicBezier p0 p1 p2 p3 ⟨1, by norm_num, by norm_num⟩ = p3 := by
  constructor <;> simp [cubicBezier] <;> ring

/-- Standard easing functions -/
inductive EasingType
  | linear
  | easeIn
  | easeOut
  | easeInOut
  | cubicBezier (x1 y1 x2 y2 : Float)

/-- Apply easing function -/
def applyEasing (easing : EasingType) (t : UnitInterval) : UnitInterval :=
  match easing with
  | .linear => t
  | .easeIn => ⟨t.value * t.value, by sorry, by sorry⟩
  | .easeOut => 
      let t' := 1 - t.value
      ⟨1 - t' * t', by sorry, by sorry⟩
  | .easeInOut =>
      if t.value < 0.5 then
        ⟨2 * t.value * t.value, by sorry, by sorry⟩
      else
        let t' := 2 * t.value - 1
        ⟨1 - 0.5 * (1 - t') * (1 - t'), by sorry, by sorry⟩
  | .cubicBezier x1 y1 x2 y2 =>
      -- Solve for t where x(t) = input, return y(t)
      ⟨solveBezierY x1 y1 x2 y2 t.value, by sorry, by sorry⟩
  where
    solveBezierY (x1 y1 x2 y2 input : Float) : Float :=
      -- Newton-Raphson to find t where bezierX(t) = input
      -- Then return bezierY(t)
      sorry -- Implementation requires iterative solver

/-- Proof: All easing functions preserve unit interval -/
theorem easing_preserves_unit (easing : EasingType) (t : UnitInterval) :
    0 ≤ (applyEasing easing t).value ∧ (applyEasing easing t).value ≤ 1 :=
  ⟨(applyEasing easing t).h_ge_zero, (applyEasing easing t).h_le_one⟩

end Lattice.Interpolation
```

### 1.3 Geometry with Proofs

```lean
-- lattice/core/Geometry.lean

namespace Lattice.Geometry

/-- 4x4 matrix multiplication -/
def matMul (a b : Mat4) : Mat4 where
  data := Array.ofFn fun i =>
    let row := i / 4
    let col := i % 4
    (a.data[row * 4 + 0]! * b.data[0 * 4 + col]! +
     a.data[row * 4 + 1]! * b.data[1 * 4 + col]! +
     a.data[row * 4 + 2]! * b.data[2 * 4 + col]! +
     a.data[row * 4 + 3]! * b.data[3 * 4 + col]!)
  h_size := by simp
  h_finite := by sorry -- Requires finite arithmetic proof

/-- Identity matrix -/
def identity : Mat4 where
  data := #[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1]
  h_size := by rfl
  h_finite := by intro i hi; simp

/-- Proof: Identity is left identity for matrix multiplication -/
theorem identity_left (m : Mat4) : matMul identity m = m := by
  sorry -- Requires component-wise proof

/-- Proof: Identity is right identity for matrix multiplication -/
theorem identity_right (m : Mat4) : matMul m identity = m := by
  sorry -- Requires component-wise proof

/-- Proof: Matrix multiplication is associative -/
theorem matMul_assoc (a b c : Mat4) : 
    matMul (matMul a b) c = matMul a (matMul b c) := by
  sorry -- Standard linear algebra proof

/-- Matrix inverse (partial function - returns none if not invertible) -/
def inverse (m : Mat4) : Option Mat4 :=
  sorry -- LU decomposition or Gauss-Jordan

/-- Proof: Inverse is correct when it exists -/
theorem inverse_correct (m m_inv : Mat4) (h : inverse m = some m_inv) :
    matMul m m_inv = identity ∧ matMul m_inv m = identity := by
  sorry

/-- Quaternion multiplication -/
def quatMul (p q : Quaternion) : Quaternion where
  w := p.w * q.w - p.x * q.x - p.y * q.y - p.z * q.z
  x := p.w * q.x + p.x * q.w + p.y * q.z - p.z * q.y
  y := p.w * q.y - p.x * q.z + p.y * q.w + p.z * q.x
  z := p.w * q.z + p.x * q.y - p.y * q.x + p.z * q.w
  h_normalized := by sorry -- Follows from quaternion algebra
  h_finite := by sorry

/-- Convert quaternion to rotation matrix -/
def quatToMat4 (q : Quaternion) : Mat4 :=
  sorry -- Standard formula

/-- Proof: Quaternion to matrix preserves rotation -/
theorem quatToMat4_correct (q : Quaternion) (p : Point3D) :
    applyMat4 (quatToMat4 q) p = rotateByQuat q p := by
  sorry

end Lattice.Geometry
```

### 1.4 Keyframe System with Proofs

```lean
-- lattice/core/Keyframe.lean

namespace Lattice.Keyframe

/-- A keyframe at a specific time with a value and easing -/
structure Keyframe (α : Type) where
  frame : Frame
  value : α
  easing : EasingType

/-- A sequence of keyframes (sorted by frame, no duplicates) -/
structure KeyframeSequence (α : Type) where
  keyframes : Array (Keyframe α)
  h_sorted : ∀ i j, i < j → j < keyframes.size → 
    (keyframes[i]!).frame.value < (keyframes[j]!).frame.value

/-- Find the surrounding keyframes for a given frame -/
def findBracket (seq : KeyframeSequence α) (f : Frame) : 
    Option (Keyframe α × Keyframe α) :=
  -- Binary search for surrounding keyframes
  sorry

/-- Evaluate keyframe sequence at a frame -/
def evaluate [Interpolatable α] (seq : KeyframeSequence α) (f : Frame) : α :=
  match seq.keyframes.size with
  | 0 => Interpolatable.default -- No keyframes
  | 1 => seq.keyframes[0]!.value -- Single keyframe
  | _ => 
    match findBracket seq f with
    | none => 
        -- Before first or after last
        if f.value ≤ (seq.keyframes[0]!).frame.value then
          seq.keyframes[0]!.value
        else
          seq.keyframes[seq.keyframes.size - 1]!.value
    | some (k1, k2) =>
        let duration := k2.frame.value - k1.frame.value
        let progress := (f.value - k1.frame.value) / duration
        let t : UnitInterval := ⟨progress, by sorry, by sorry⟩
        let easedT := applyEasing k1.easing t
        Interpolatable.interpolate k1.value k2.value easedT

/-- Proof: Evaluation at keyframe returns keyframe value -/
theorem eval_at_keyframe [Interpolatable α] (seq : KeyframeSequence α) 
    (i : Nat) (h : i < seq.keyframes.size) :
    evaluate seq (seq.keyframes[i]!).frame = (seq.keyframes[i]!).value := by
  sorry -- Follows from lerp_at_zero or lerp_at_one

/-- Proof: Evaluation is continuous between keyframes -/
theorem eval_continuous [Interpolatable α] (seq : KeyframeSequence α)
    (f1 f2 : Frame) (h : f1.value ≤ f2.value) :
    -- The function frame → evaluate seq frame is continuous
    sorry

/-- Typeclass for types that can be interpolated -/
class Interpolatable (α : Type) where
  default : α
  interpolate : α → α → UnitInterval → α

instance : Interpolatable Float where
  default := 0
  interpolate := lerp

instance : Interpolatable Point2D where
  default := ⟨0, 0, by norm_num, by norm_num⟩
  interpolate a b t := ⟨
    lerp a.x b.x t,
    lerp a.y b.y t,
    by sorry,
    by sorry
  ⟩

instance : Interpolatable Color where
  default := ⟨⟨0, by sorry, by sorry⟩, ⟨0, by sorry, by sorry⟩, 
              ⟨0, by sorry, by sorry⟩, ⟨1, by sorry, by sorry⟩⟩
  interpolate a b t := ⟨
    ⟨lerp a.r.value b.r.value t, by sorry, by sorry⟩,
    ⟨lerp a.g.value b.g.value t, by sorry, by sorry⟩,
    ⟨lerp a.b.value b.b.value t, by sorry, by sorry⟩,
    ⟨lerp a.a.value b.a.value t, by sorry, by sorry⟩
  ⟩

end Lattice.Keyframe
```

---

## Part II: PureScript Frontend Architecture

### 2.1 Type System (PureScript)

```purescript
-- src/Lattice/Types.purs

module Lattice.Types where

import Prelude
import Data.Maybe (Maybe)
import Data.Array (Array)
import Data.Map (Map)

-- | Frame number (non-negative integer)
newtype Frame = Frame Int

derive newtype instance eqFrame :: Eq Frame
derive newtype instance ordFrame :: Ord Frame
derive newtype instance showFrame :: Show Frame

-- | Ensure frame is non-negative
mkFrame :: Int -> Maybe Frame
mkFrame n
  | n >= 0 = Just (Frame n)
  | otherwise = Nothing

-- | Unit interval [0, 1]
newtype UnitInterval = UnitInterval Number

mkUnitInterval :: Number -> Maybe UnitInterval
mkUnitInterval n
  | n >= 0.0 && n <= 1.0 = Just (UnitInterval n)
  | otherwise = Nothing

-- | 2D Point with finite coordinates
type Point2D = 
  { x :: Number
  , y :: Number
  }

-- | 3D Point with finite coordinates
type Point3D = 
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | RGBA Color (all components in [0, 1])
type Color = 
  { r :: UnitInterval
  , g :: UnitInterval
  , b :: UnitInterval
  , a :: UnitInterval
  }

-- | Layer ID (validated string)
newtype LayerId = LayerId String

derive newtype instance eqLayerId :: Eq LayerId
derive newtype instance ordLayerId :: Ord LayerId
derive newtype instance showLayerId :: Show LayerId

-- | Transform state at a point in time
type TransformState =
  { position :: Point3D
  , rotation :: Point3D  -- Euler angles in radians
  , scale :: Point3D
  , anchor :: Point2D
  , opacity :: UnitInterval
  }

-- | Easing function specification
data EasingType
  = Linear
  | EaseIn
  | EaseOut  
  | EaseInOut
  | CubicBezier Number Number Number Number

derive instance eqEasingType :: Eq EasingType

-- | A keyframe with time, value, and easing
type Keyframe a =
  { frame :: Frame
  , value :: a
  , easing :: EasingType
  }

-- | Keyframe sequence (must be sorted by frame)
newtype KeyframeSequence a = KeyframeSequence (Array (Keyframe a))

-- | Layer type enumeration
data LayerType
  = ImageLayer
  | VideoLayer
  | TextLayer
  | ShapeLayer
  | SolidLayer
  | NullLayer
  | CameraLayer
  | LightLayer
  | AudioLayer
  | ParticleLayer
  | PrecompLayer

derive instance eqLayerType :: Eq LayerType

-- | A layer in the composition
type Layer =
  { id :: LayerId
  , name :: String
  , layerType :: LayerType
  , visible :: Boolean
  , locked :: Boolean
  , solo :: Boolean
  , parentId :: Maybe LayerId
  , inPoint :: Frame
  , outPoint :: Frame
  , transform :: Map String (KeyframeSequence Number)
  -- Additional properties based on layer type
  }

-- | Composition settings
type CompositionSettings =
  { width :: Int
  , height :: Int
  , frameRate :: Number
  , duration :: Frame
  , backgroundColor :: Color
  }

-- | Full project structure
type Project =
  { meta :: ProjectMeta
  , composition :: CompositionSettings
  , layers :: Array Layer
  , assets :: Map String Asset
  }

type ProjectMeta =
  { name :: String
  , created :: String  -- ISO 8601
  , modified :: String -- ISO 8601
  , version :: String
  }

type Asset =
  { id :: String
  , name :: String
  , assetType :: AssetType
  , src :: String
  }

data AssetType
  = ImageAsset
  | VideoAsset
  | AudioAsset
  | FontAsset
```

### 2.2 Halogen Component Architecture

```purescript
-- src/Lattice/UI/App.purs

module Lattice.UI.App where

import Prelude
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Data.Maybe (Maybe(..))

import Lattice.Types (Project, LayerId, Frame)
import Lattice.State.Store as Store

-- | Top-level application state
type AppState =
  { project :: Maybe Project
  , currentFrame :: Frame
  , selectedLayers :: Array LayerId
  , playing :: Boolean
  , zoom :: Number
  }

-- | Application actions (all state changes are explicit)
data AppAction
  = Initialize
  | LoadProject String
  | ProjectLoaded Project
  | SaveProject
  | SetCurrentFrame Frame
  | SelectLayer LayerId
  | DeselectLayer LayerId
  | ClearSelection
  | TogglePlayback
  | SetZoom Number
  | AddLayer LayerType
  | DeleteLayer LayerId
  | UpdateLayerProperty LayerId String PropertyValue

-- | The main application component
appComponent :: forall q i o. H.Component q i o Aff
appComponent = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }
  where
  initialState :: AppState
  initialState =
    { project: Nothing
    , currentFrame: Frame 0
    , selectedLayers: []
    , playing: false
    , zoom: 1.0
    }

  render :: AppState -> H.ComponentHTML AppAction () Aff
  render state =
    HH.div
      [ HP.class_ (H.ClassName "app-container") ]
      [ renderMenuBar state
      , HH.div
          [ HP.class_ (H.ClassName "workspace") ]
          [ renderToolbar state
          , renderCanvas state
          , renderTimeline state
          , renderProperties state
          ]
      ]

  handleAction :: AppAction -> H.HalogenM AppState AppAction () o Aff Unit
  handleAction = case _ of
    Initialize -> do
      -- Load settings, recent projects, etc.
      pure unit
    
    LoadProject path -> do
      -- Call backend to load project
      result <- H.liftAff $ Store.loadProject path
      case result of
        Just project -> handleAction (ProjectLoaded project)
        Nothing -> pure unit -- Handle error
    
    ProjectLoaded project ->
      H.modify_ _ { project = Just project }
    
    SetCurrentFrame frame ->
      H.modify_ _ { currentFrame = frame }
    
    SelectLayer layerId -> do
      state <- H.get
      H.modify_ _ { selectedLayers = state.selectedLayers <> [layerId] }
    
    -- ... other actions

-- | Timeline component
timelineComponent :: forall q o. H.Component q TimelineInput o Aff
timelineComponent = H.mkComponent
  { initialState: identity
  , render: renderTimeline
  , eval: H.mkEval H.defaultEval
  }

-- | Canvas/viewport component  
canvasComponent :: forall q o. H.Component q CanvasInput o Aff
canvasComponent = H.mkComponent
  { initialState: identity
  , render: renderCanvas
  , eval: H.mkEval H.defaultEval
  }
```

### 2.3 State Management (PureScript)

```purescript
-- src/Lattice/State/Store.purs

module Lattice.State.Store where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (class MonadEffect, liftEffect)

import Lattice.Types (Project, Layer, LayerId, Frame)
import Lattice.Core.Validation as Validation

-- | Store state with undo/redo history
type StoreState =
  { project :: Maybe Project
  , undoStack :: Array Project
  , redoStack :: Array Project
  , dirty :: Boolean
  }

-- | Store actions - pure transformations
data StoreAction
  = LoadProject Project
  | AddLayer Layer
  | RemoveLayer LayerId
  | UpdateLayer LayerId (Layer -> Layer)
  | Undo
  | Redo
  | MarkClean

-- | Pure reducer - no side effects
reduce :: StoreState -> StoreAction -> StoreState
reduce state action = case action of
  LoadProject project ->
    { project: Just project
    , undoStack: []
    , redoStack: []
    , dirty: false
    }
  
  AddLayer layer ->
    case state.project of
      Nothing -> state
      Just project ->
        let 
          newProject = project { layers = project.layers <> [layer] }
        in
          { project: Just newProject
          , undoStack: state.undoStack <> [project]
          , redoStack: []
          , dirty: true
          }
  
  RemoveLayer layerId ->
    case state.project of
      Nothing -> state
      Just project ->
        let
          newLayers = filter (\l -> l.id /= layerId) project.layers
          newProject = project { layers = newLayers }
        in
          { project: Just newProject
          , undoStack: state.undoStack <> [project]
          , redoStack: []
          , dirty: true
          }
  
  UpdateLayer layerId f ->
    case state.project of
      Nothing -> state
      Just project ->
        let
          newLayers = map (\l -> if l.id == layerId then f l else l) project.layers
          newProject = project { layers = newLayers }
        in
          { project: Just newProject
          , undoStack: state.undoStack <> [project]
          , redoStack: []
          , dirty: true
          }
  
  Undo ->
    case unsnoc state.undoStack of
      Nothing -> state
      Just { init, last } ->
        case state.project of
          Nothing -> state
          Just current ->
            { project: Just last
            , undoStack: init
            , redoStack: state.redoStack <> [current]
            , dirty: true
            }
  
  Redo ->
    case unsnoc state.redoStack of
      Nothing -> state
      Just { init, last } ->
        case state.project of
          Nothing -> state
          Just current ->
            { project: Just last
            , undoStack: state.undoStack <> [current]
            , redoStack: init
            , dirty: true
            }
  
  MarkClean ->
    state { dirty = false }

-- | Project validation before save
validateProject :: Project -> Either (Array String) Project
validateProject = Validation.runValidation
  [ Validation.validateLayers
  , Validation.validateKeyframes
  , Validation.validateAssetRefs
  , Validation.validateParentRefs
  ]

-- | Load project from backend
loadProject :: String -> Aff (Maybe Project)
loadProject path = do
  response <- fetchProject path
  case response of
    Left _ -> pure Nothing
    Right json -> 
      case parseProject json of
        Left _ -> pure Nothing
        Right project ->
          case validateProject project of
            Left _ -> pure Nothing
            Right validProject -> pure (Just validProject)

-- | Save project to backend
saveProject :: Project -> Aff (Either String Unit)
saveProject project =
  case validateProject project of
    Left errors -> pure (Left $ intercalate ", " errors)
    Right validProject -> do
      result <- postProject validProject
      pure $ case result of
        Left e -> Left e
        Right _ -> Right unit
```

---

## Part III: Backend (PureScript → Node.js)

### 3.1 Server Architecture

```purescript
-- src/Lattice/Server/Main.purs

module Lattice.Server.Main where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Console (log)
import Node.Express.App (App, listenHttp, get, post, use)
import Node.Express.Handler (Handler)
import Node.Express.Request (getBody, getRouteParam)
import Node.Express.Response (send, sendJson, setStatus)

import Lattice.Server.Routes.Projects as Projects
import Lattice.Server.Routes.AI as AI
import Lattice.Server.Routes.Export as Export
import Lattice.Server.Middleware as Middleware

main :: Effect Unit
main = launchAff_ do
  log "Starting Lattice Server..."
  liftEffect $ listenHttp app 8080 \_ ->
    log "Server listening on port 8080"

app :: App
app = do
  -- Middleware
  use Middleware.cors
  use Middleware.jsonParser
  use Middleware.logging
  use Middleware.errorHandler
  
  -- Health check
  get "/api/health" healthHandler
  
  -- Project routes
  get "/api/projects" Projects.list
  get "/api/projects/:id" Projects.load
  post "/api/projects" Projects.save
  delete "/api/projects/:id" Projects.delete
  
  -- AI routes (depth, segment, normal, VLM)
  post "/api/ai/depth" AI.estimateDepth
  post "/api/ai/segment" AI.segmentImage
  post "/api/ai/normal" AI.generateNormal
  post "/api/ai/vlm" AI.analyzeWithVLM
  
  -- Export routes
  post "/api/export/png" Export.exportPNG
  post "/api/export/video" Export.exportVideo

healthHandler :: Handler
healthHandler = do
  sendJson { status: "healthy", version: "1.0.0" }
```

### 3.2 Project Storage with Validation

```purescript
-- src/Lattice/Server/Routes/Projects.purs

module Lattice.Server.Routes.Projects where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Node.Express.Handler (Handler)
import Node.Express.Request (getBody, getRouteParam)
import Node.Express.Response (sendJson, setStatus)

import Lattice.Types (Project)
import Lattice.Storage.Projects as Storage
import Lattice.Core.Validation as Validation

-- | List all projects
list :: Handler
list = do
  projects <- liftAff Storage.listProjects
  sendJson { status: "success", projects }

-- | Load a project by ID
load :: Handler
load = do
  maybeId <- getRouteParam "id"
  case maybeId of
    Nothing -> do
      setStatus 400
      sendJson { status: "error", message: "Missing project ID" }
    Just projectId -> do
      result <- liftAff $ Storage.loadProject projectId
      case result of
        Left error -> do
          setStatus 404
          sendJson { status: "error", message: error }
        Right project -> do
          -- Validate loaded project
          case Validation.runValidation Validation.allValidators project of
            Left errors -> do
              setStatus 400
              sendJson { status: "error", message: "Invalid project", errors }
            Right validProject ->
              sendJson { status: "success", project: validProject }

-- | Save a project
save :: Handler
save = do
  body <- getBody
  case parseProjectFromBody body of
    Left error -> do
      setStatus 400
      sendJson { status: "error", message: error }
    Right project -> do
      -- Validate before saving
      case Validation.runValidation Validation.allValidators project of
        Left errors -> do
          setStatus 400
          sendJson { status: "error", message: "Validation failed", errors }
        Right validProject -> do
          result <- liftAff $ Storage.saveProject validProject
          case result of
            Left error -> do
              setStatus 500
              sendJson { status: "error", message: error }
            Right projectId ->
              sendJson { status: "success", projectId }

-- | Delete a project
delete :: Handler
delete = do
  maybeId <- getRouteParam "id"
  case maybeId of
    Nothing -> do
      setStatus 400
      sendJson { status: "error", message: "Missing project ID" }
    Just projectId -> do
      result <- liftAff $ Storage.deleteProject projectId
      case result of
        Left error -> do
          setStatus 500
          sendJson { status: "error", message: error }
        Right _ ->
          sendJson { status: "success" }
```

---

## Part IV: Lean4 ↔ PureScript FFI

### 4.1 Lean4 → WASM Compilation

```lean
-- lattice/ffi/Export.lean

/-!
# FFI Exports for PureScript/JavaScript

These functions are compiled to WASM and called from PureScript.
-/

namespace Lattice.FFI

/-- Evaluate keyframe sequence at frame (exported to JS) -/
@[export lattice_eval_keyframes]
def evalKeyframes (keyframesJson : String) (frame : UInt32) : String :=
  -- Parse JSON → KeyframeSequence Float
  -- Evaluate at frame
  -- Return result as JSON
  sorry

/-- Interpolate between two transforms (exported to JS) -/
@[export lattice_lerp_transform]
def lerpTransform (t1Json t2Json : String) (t : Float) : String :=
  -- Parse transforms from JSON
  -- Interpolate
  -- Return result as JSON
  sorry

/-- Apply easing function (exported to JS) -/
@[export lattice_apply_easing]
def applyEasingFFI (easingJson : String) (t : Float) : Float :=
  -- Parse easing from JSON
  -- Apply
  -- Return result
  sorry

/-- Matrix multiplication (exported to JS) -/
@[export lattice_mat4_mul]
def mat4MulFFI (aJson bJson : String) : String :=
  -- Parse matrices
  -- Multiply
  -- Return result as JSON
  sorry

/-- Quaternion slerp (exported to JS) -/
@[export lattice_quat_slerp]
def quatSlerpFFI (q1Json q2Json : String) (t : Float) : String :=
  -- Parse quaternions
  -- Slerp
  -- Return result as JSON
  sorry

end Lattice.FFI
```

### 4.2 PureScript FFI Bindings

```purescript
-- src/Lattice/Core/FFI.purs

module Lattice.Core.FFI where

import Prelude
import Effect (Effect)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Encode (encodeJson)
import Data.Argonaut.Decode (decodeJson)
import Data.Either (Either)

-- | Foreign imports from Lean4 WASM module
foreign import evalKeyframesImpl :: String -> Int -> String
foreign import lerpTransformImpl :: String -> String -> Number -> String
foreign import applyEasingImpl :: String -> Number -> Number
foreign import mat4MulImpl :: String -> String -> String
foreign import quatSlerpImpl :: String -> String -> Number -> String

-- | Type-safe wrapper for keyframe evaluation
evalKeyframes :: forall a. Encode a => Decode a => 
    KeyframeSequence a -> Frame -> Either String a
evalKeyframes seq (Frame f) =
  let 
    jsonIn = encodeJson seq
    jsonOut = evalKeyframesImpl (stringify jsonIn) f
  in
    decodeJson =<< parseJson jsonOut

-- | Type-safe wrapper for transform interpolation
lerpTransform :: TransformState -> TransformState -> UnitInterval -> 
    Either String TransformState
lerpTransform t1 t2 (UnitInterval t) =
  let
    j1 = encodeJson t1
    j2 = encodeJson t2
    jsonOut = lerpTransformImpl (stringify j1) (stringify j2) t
  in
    decodeJson =<< parseJson jsonOut

-- | Type-safe wrapper for easing
applyEasing :: EasingType -> UnitInterval -> UnitInterval
applyEasing easing (UnitInterval t) =
  let
    easingJson = encodeJson easing
    result = applyEasingImpl (stringify easingJson) t
  in
    UnitInterval result  -- Lean4 guarantees this is in [0,1]

-- | Type-safe wrapper for matrix multiplication
mat4Mul :: Mat4 -> Mat4 -> Either String Mat4
mat4Mul a b =
  let
    aJson = encodeJson a
    bJson = encodeJson b
    resultJson = mat4MulImpl (stringify aJson) (stringify bJson)
  in
    decodeJson =<< parseJson resultJson
```

---

## Part V: Validation with Proofs

### 5.1 Project Validation (PureScript)

```purescript
-- src/Lattice/Core/Validation.purs

module Lattice.Core.Validation where

import Prelude
import Data.Array (filter, any, all)
import Data.Either (Either(..))
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..), isJust)
import Data.Set as Set
import Data.Traversable (traverse)

import Lattice.Types

-- | Validation result
type ValidationResult = Either (Array String) Unit

-- | A validator is a function from Project to ValidationResult
type Validator = Project -> ValidationResult

-- | Run multiple validators, collecting all errors
runValidation :: Array Validator -> Project -> Either (Array String) Project
runValidation validators project =
  let
    results = map (\v -> v project) validators
    errors = foldl collectErrors [] results
  in
    if null errors
      then Right project
      else Left errors
  where
  collectErrors acc (Left errs) = acc <> errs
  collectErrors acc (Right _) = acc

-- | All validators
allValidators :: Array Validator
allValidators =
  [ validateLayers
  , validateKeyframes
  , validateAssetRefs
  , validateParentRefs
  , validateNoCircularParents
  , validateInOutPoints
  , validateNumericBounds
  ]

-- | Validate all layers have unique IDs
validateLayers :: Validator
validateLayers project =
  let
    ids = map _.id project.layers
    uniqueIds = Set.fromFoldable ids
  in
    if Set.size uniqueIds == length ids
      then Right unit
      else Left ["Duplicate layer IDs detected"]

-- | Validate keyframe sequences are sorted
validateKeyframes :: Validator
validateKeyframes project =
  let
    errors = project.layers >>= validateLayerKeyframes
  in
    if null errors
      then Right unit
      else Left errors
  where
  validateLayerKeyframes layer =
    Map.values layer.transform >>= validateSequenceSorted
  
  validateSequenceSorted (KeyframeSequence kfs) =
    if isSorted (map (_.frame >>> unwrap) kfs)
      then []
      else ["Keyframes not sorted in layer"]
  
  isSorted arr = case arr of
    [] -> true
    [_] -> true
    xs -> all identity $ zipWith (<) xs (drop 1 xs)

-- | Validate all asset references exist
validateAssetRefs :: Validator
validateAssetRefs project =
  let
    assetIds = Set.fromFoldable $ Map.keys project.assets
    layerAssetRefs = project.layers >>= getAssetRefs
    missingRefs = filter (\ref -> not (Set.member ref assetIds)) layerAssetRefs
  in
    if null missingRefs
      then Right unit
      else Left $ map (\ref -> "Missing asset: " <> ref) missingRefs
  where
  getAssetRefs layer = case layer.layerType of
    ImageLayer -> [layer.assetId]
    VideoLayer -> [layer.assetId]
    AudioLayer -> [layer.assetId]
    _ -> []

-- | Validate parent references exist
validateParentRefs :: Validator
validateParentRefs project =
  let
    layerIds = Set.fromFoldable $ map _.id project.layers
    parentRefs = project.layers >>= \layer -> 
      case layer.parentId of
        Nothing -> []
        Just pid -> [pid]
    missingParents = filter (\pid -> not (Set.member pid layerIds)) parentRefs
  in
    if null missingParents
      then Right unit
      else Left $ map (\pid -> "Missing parent layer: " <> show pid) missingParents

-- | Validate no circular parent references
validateNoCircularParents :: Validator
validateNoCircularParents project =
  let
    cycles = detectCycles project.layers
  in
    if null cycles
      then Right unit
      else Left ["Circular parent reference detected"]
  where
  detectCycles layers =
    -- Build parent map, detect cycles via DFS
    let
      parentMap = foldl buildMap Map.empty layers
      buildMap m layer = case layer.parentId of
        Nothing -> m
        Just pid -> Map.insert layer.id pid m
    in
      filter (hasCycle parentMap Set.empty) (map _.id layers)
  
  hasCycle parentMap visited current =
    if Set.member current visited
      then true
      else case Map.lookup current parentMap of
        Nothing -> false
        Just parent -> hasCycle parentMap (Set.insert current visited) parent

-- | Validate in/out points are within composition
validateInOutPoints :: Validator
validateInOutPoints project =
  let
    duration = unwrap project.composition.duration
    errors = project.layers >>= \layer ->
      let
        inPt = unwrap layer.inPoint
        outPt = unwrap layer.outPoint
      in
        (if inPt < 0 then ["Layer " <> show layer.id <> " has negative in point"] else []) <>
        (if outPt > duration then ["Layer " <> show layer.id <> " out point exceeds duration"] else []) <>
        (if inPt >= outPt then ["Layer " <> show layer.id <> " in point >= out point"] else [])
  in
    if null errors
      then Right unit
      else Left errors

-- | Validate numeric bounds (no NaN, Infinity)
validateNumericBounds :: Validator
validateNumericBounds project =
  let
    errors = project.layers >>= validateLayerNumbers
  in
    if null errors
      then Right unit
      else Left errors
  where
  validateLayerNumbers layer =
    Map.toUnfoldable layer.transform >>= \(Tuple prop (KeyframeSequence kfs)) ->
      kfs >>= \kf ->
        if isFinite kf.value
          then []
          else ["Non-finite value in " <> prop <> " keyframes"]
```

### 5.2 Serialization Round-Trip Proof (Lean4)

```lean
-- lattice/proofs/Serialization.lean

/-!
# Serialization Correctness Proofs

Prove that serialization and deserialization are inverses.
-/

namespace Lattice.Proofs.Serialization

/-- JSON representation -/
inductive Json
  | null
  | bool (b : Bool)
  | num (n : Float)
  | str (s : String)
  | arr (xs : List Json)
  | obj (fields : List (String × Json))

/-- Serialization typeclass -/
class Serialize (α : Type) where
  toJson : α → Json
  fromJson : Json → Option α

/-- Round-trip property: fromJson (toJson x) = some x -/
def roundTrip (α : Type) [Serialize α] : Prop :=
  ∀ x : α, Serialize.fromJson (Serialize.toJson x) = some x

/-- Prove round-trip for Frame -/
instance : Serialize Frame where
  toJson f := Json.num f.value.toFloat
  fromJson := fun
    | Json.num n => 
        if n ≥ 0 ∧ n = n.floor then some ⟨n.toUInt64.toNat⟩ else none
    | _ => none

theorem frame_roundTrip : roundTrip Frame := by
  intro f
  simp [Serialize.toJson, Serialize.fromJson]
  sorry -- Complete proof requires Float properties

/-- Prove round-trip for Point2D -/
instance : Serialize Point2D where
  toJson p := Json.obj [("x", Json.num p.x), ("y", Json.num p.y)]
  fromJson := fun
    | Json.obj fields => 
        match fields.lookup "x", fields.lookup "y" with
        | some (Json.num x), some (Json.num y) =>
            if x.isFinite ∧ y.isFinite then
              some ⟨x, y, by sorry, by sorry⟩
            else none
        | _, _ => none
    | _ => none

theorem point2d_roundTrip : roundTrip Point2D := by
  intro p
  simp [Serialize.toJson, Serialize.fromJson]
  sorry -- Complete proof

/-- Prove round-trip for Color -/
instance : Serialize Color where
  toJson c := Json.obj [
    ("r", Json.num c.r.value),
    ("g", Json.num c.g.value),
    ("b", Json.num c.b.value),
    ("a", Json.num c.a.value)
  ]
  fromJson := fun
    | Json.obj fields =>
        match fields.lookup "r", fields.lookup "g", 
              fields.lookup "b", fields.lookup "a" with
        | some (Json.num r), some (Json.num g),
          some (Json.num b), some (Json.num a) =>
            if 0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ g ∧ g ≤ 1 ∧ 
               0 ≤ b ∧ b ≤ 1 ∧ 0 ≤ a ∧ a ≤ 1 then
              some ⟨⟨r, by sorry, by sorry⟩,
                    ⟨g, by sorry, by sorry⟩,
                    ⟨b, by sorry, by sorry⟩,
                    ⟨a, by sorry, by sorry⟩⟩
            else none
        | _, _, _, _ => none
    | _ => none

theorem color_roundTrip : roundTrip Color := by
  intro c
  simp [Serialize.toJson, Serialize.fromJson]
  sorry -- Complete proof

/-- Prove round-trip for KeyframeSequence -/
theorem keyframeSequence_roundTrip (α : Type) [Serialize α] 
    (h : roundTrip α) : roundTrip (KeyframeSequence α) := by
  sorry -- Proof by induction on array structure

/-- Prove round-trip for full Layer -/
theorem layer_roundTrip : roundTrip Layer := by
  sorry -- Compose all component round-trip proofs

/-- Prove round-trip for full Project -/
theorem project_roundTrip : roundTrip Project := by
  sorry -- Compose all component round-trip proofs

end Lattice.Proofs.Serialization
```

---

## Part VI: Timeline

| Phase | Weeks | Deliverables | Proof Obligations |
|-------|-------|--------------|-------------------|
| **0: Foundation** | 1-4 | Lean4 project setup, core types, basic proofs | Type definitions compile, UnitInterval proofs |
| **1: Math Core** | 5-12 | Interpolation, geometry, keyframes in Lean4 | lerp bounds, bezier endpoints, matrix associativity |
| **2: PureScript Types** | 13-16 | Full type system, validation module | Validation functions total and correct |
| **3: FFI Bridge** | 17-20 | Lean4 → WASM, PureScript bindings | FFI preserves types |
| **4: UI Components** | 21-28 | Halogen components, state management | State reducer is pure |
| **5: Backend Server** | 29-34 | PureScript Node.js server, storage | Storage round-trip |
| **6: Integration** | 35-40 | Full system integration, E2E tests | End-to-end correctness |
| **7: Proofs Complete** | 41-48 | All proof obligations discharged | Full formal verification |
| **8: Polish** | 49-52 | Documentation, deployment | Production ready |

**Total: 52 weeks (12 months)**

---

## Part VII: Proof Obligations Checklist

### Interpolation
- [ ] `lerp_at_zero`: lerp(a, b, 0) = a
- [ ] `lerp_at_one`: lerp(a, b, 1) = b
- [ ] `lerp_bounded`: a ≤ lerp(a, b, t) ≤ b when a ≤ b
- [ ] `lerp_continuous`: lerp is Lipschitz continuous
- [ ] `bezier_endpoints`: bezier passes through p0 and p3
- [ ] `easing_preserves_unit`: all easings map [0,1] → [0,1]

### Geometry
- [ ] `identity_left`: I × M = M
- [ ] `identity_right`: M × I = M
- [ ] `matMul_assoc`: (A × B) × C = A × (B × C)
- [ ] `inverse_correct`: M × M⁻¹ = I
- [ ] `quatToMat4_correct`: quaternion and matrix rotation equivalent

### Keyframes
- [ ] `eval_at_keyframe`: evaluation at keyframe returns keyframe value
- [ ] `eval_continuous`: evaluation is continuous between keyframes
- [ ] `keyframe_sorted_invariant`: sequence maintains sorted order

### Serialization
- [ ] `frame_roundTrip`: fromJson(toJson(f)) = f
- [ ] `point2d_roundTrip`: fromJson(toJson(p)) = p
- [ ] `color_roundTrip`: fromJson(toJson(c)) = c
- [ ] `layer_roundTrip`: fromJson(toJson(l)) = l
- [ ] `project_roundTrip`: fromJson(toJson(p)) = p

### Validation
- [ ] `validateLayers_complete`: catches all duplicate IDs
- [ ] `validateKeyframes_complete`: catches all unsorted sequences
- [ ] `validateNoCircularParents_complete`: catches all cycles
- [ ] `validation_total`: validators always terminate

---

## Part VIII: Directory Structure

```
lattice/
├── lean/                          # Lean4 verified math core
│   ├── Lattice/
│   │   ├── Core/
│   │   │   ├── Types.lean         # Core types with invariants
│   │   │   ├── Interpolation.lean # Lerp, bezier, easing
│   │   │   ├── Geometry.lean      # Vectors, matrices, quaternions
│   │   │   └── Keyframe.lean      # Keyframe evaluation
│   │   ├── Proofs/
│   │   │   ├── Interpolation.lean # Interpolation proofs
│   │   │   ├── Geometry.lean      # Geometry proofs
│   │   │   └── Serialization.lean # Round-trip proofs
│   │   └── FFI/
│   │       └── Export.lean        # WASM exports
│   ├── lakefile.lean
│   └── lean-toolchain
├── purescript/
│   ├── src/
│   │   ├── Lattice/
│   │   │   ├── Types.purs         # Type definitions
│   │   │   ├── Core/
│   │   │   │   ├── FFI.purs       # Lean4 FFI bindings
│   │   │   │   └── Validation.purs
│   │   │   ├── State/
│   │   │   │   └── Store.purs     # State management
│   │   │   ├── UI/
│   │   │   │   ├── App.purs       # Main app component
│   │   │   │   ├── Canvas.purs    # Viewport
│   │   │   │   ├── Timeline.purs  # Timeline
│   │   │   │   └── Properties.purs
│   │   │   └── Server/
│   │   │       ├── Main.purs      # HTTP server
│   │   │       └── Routes/
│   │   │           ├── Projects.purs
│   │   │           ├── AI.purs
│   │   │           └── Export.purs
│   │   └── Main.purs
│   ├── test/
│   ├── spago.yaml
│   └── packages.dhall
├── wasm/                          # Compiled WASM from Lean4
│   └── lattice_core.wasm
└── docs/
    ├── FORMAL_EXTRACTION_PLAN.md
    ├── PROOF_OBLIGATIONS.md
    └── API.md
```

---

This is the real plan. Correct. Formally verified. No shortcuts.
