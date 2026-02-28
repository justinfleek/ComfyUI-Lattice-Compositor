/-
  Hydrogen - Root Module for Lean4 Proofs
  
  THE PUREST WEB DESIGN LANGUAGE EVER CREATED.
  
  This module aggregates all Hydrogen proofs:
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ Schema.Color    │ Hue wrapping, color space conversions, WCAG contrast    │
  │ Math            │ Vec3, Vec4, Mat3, Mat4, Quaternion, Euler, Ray, Plane,  │
  │                 │ Box3, Sphere, Triangle, Frustum, Integration, Force     │
  │ Scene           │ Node, Graph, Resource, Diff (solves Three.js pain)      │
  │ Geometry        │ Vertex, Mesh, Primitives, Bounds, Texture               │
  │ Camera          │ Types, Lens, Projection (FOV ↔ focal length, matrices)  │
  │ Light           │ Types, Attenuation, Directional, Point, Spot, Shadow    │
  │ Material        │ Types, Layer, BRDF, Sparkle, ISP (NVIDIA PPISP-based)   │
  │ WorldModel      │ Pose, Attention (AnchorWeave-based spatial memory)      │
  │ Optimize        │ Submodular maximization, matroids, FAA algorithm        │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  Status: 
    - Schema.Color: Complete
    - Math: 19 modules complete (full 3D math foundation)
    - Scene: 4 modules complete (scene graph architecture)
    - Geometry: 5 modules complete (procedural mesh + texture sampling)
    - Camera: 3 modules complete (camera system with proven invariants)
    - Light: 6 modules complete (light system with attenuation proofs)
    - Material: 5 modules complete (PBR + sparkle + ISP)
    - WorldModel: 2 modules (spatial memory security proofs)
    - Optimize: 4 modules (submodular, matroid, continuous greedy, FAA)
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCHEMA (Design System Ontology)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Color.Hue
import Hydrogen.Schema.Color.Conversions
import Hydrogen.Schema.Color.OnoSendai
import Hydrogen.Schema.Diff
import Hydrogen.Schema.Group
import Hydrogen.Schema.Priority

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATH (3D Primitives with Zero-Latency Invariants)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCENE (Scene Graph Architecture)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Scene

-- ═══════════════════════════════════════════════════════════════════════════════
-- GEOMETRY (Procedural Mesh Generation)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Geometry

-- ═══════════════════════════════════════════════════════════════════════════════
-- CAMERA (Camera System with Proven Invariants)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Camera

-- ═══════════════════════════════════════════════════════════════════════════════
-- LIGHT (Light System with Attenuation Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Light

-- ═══════════════════════════════════════════════════════════════════════════════
-- MATERIAL (PBR Materials with Deep BRDF Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Material

-- ═══════════════════════════════════════════════════════════════════════════════
-- WORLDMODEL (Spatial Memory Security for Virtual Environments)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.WorldModel

-- ═══════════════════════════════════════════════════════════════════════════════
-- OPTIMIZE (Submodular Maximization for GPU Resource Allocation)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Optimize

-- ═══════════════════════════════════════════════════════════════════════════════
-- GPU (GPU Precision and Quantization Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.Precision
import Hydrogen.GPU.Landauer
import Hydrogen.GPU.Diffusion

-- ═══════════════════════════════════════════════════════════════════════════════
-- SCALE (Billion-Agent Coordination Proofs)
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Scale