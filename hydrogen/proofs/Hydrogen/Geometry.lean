/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          HYDROGEN // GEOMETRY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Procedural geometry generation for Hydrogen.
  
  This module provides the geometry infrastructure for creating meshes,
  with proven vertex/index counts and proper bounding volume computation.
  
  Key design decisions:
  - All geometry is defined as pure data (MeshDescriptor)
  - Vertex layouts are type-safe with proven stride calculations
  - Bounding volumes are computed with proven containment
  - Procedural generators have proven vertex/index count formulas
  
  ─────────────────────────────────────────────────────────────────────────────
  MODULES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Vertex      : Vertex attribute types, formats, and layouts
  - Mesh        : MeshDescriptor, Submesh, InstanceData
  - Primitives  : Box, Plane, Sphere, Cylinder generators
  - Bounds      : AABB and bounding sphere computation
  - Texture     : UV wrap modes, bilinear interpolation, mipmapping
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Geometry.Vertex
import Hydrogen.Geometry.Mesh
import Hydrogen.Geometry.Primitives
import Hydrogen.Geometry.Bounds
import Hydrogen.Geometry.Texture
