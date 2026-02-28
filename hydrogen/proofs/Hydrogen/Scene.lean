/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            HYDROGEN // SCENE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Scene graph architecture for Hydrogen.
  
  This module provides the core scene management infrastructure that addresses
  the architectural pain points of Three.js:
  
  1. **Memory Leaks / Manual Disposal Hell** (Resource.lean)
     - Pure functional architecture: no mutable state, no manual disposal
     - ResourceDelta computes exact add/remove operations
     - Runtime manages resources automatically based on data reachability
  
  2. **Scene Graph Traversal Performance** (Graph.lean, Diff.lean)
     - Incremental matrix updates with dirty tracking
     - Diff/patch only what changes
     - Static scene = zero work per frame
  
  3. **Type Safety** (Node.lean)
     - Immutable transform data with proven properties
     - Operations return new values (no mutation bugs)
     - World matrix computation proven associative
  
  ─────────────────────────────────────────────────────────────────────────────
  MODULES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Node       : Transform nodes with local/world matrix computation
  - Graph      : Scene graph structure with traversal operations
  - Resource   : Automatic resource lifecycle and delta computation
  - Diff       : Structural diffing for incremental updates
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Scene.Node
import Hydrogen.Scene.Graph
import Hydrogen.Scene.Resource
import Hydrogen.Scene.Diff
