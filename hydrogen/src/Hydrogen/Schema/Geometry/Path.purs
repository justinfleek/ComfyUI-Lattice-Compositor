-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geometry // path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Path — SVG path commands composed into vector graphics.
-- |
-- | This is the leader module that re-exports all Path submodules.
-- |
-- | ## Submodules
-- |
-- | - Path.Types: Core types (PathCommand, Path, ArcParams)
-- | - Path.Construction: Path builders (emptyPath, moveTo, lineTo, etc.)
-- | - Path.Query: Inspection functions (isEmpty, isClosed, firstPoint, etc.)
-- | - Path.Serialization: SVG export (toSvgString)
-- | - Path.Geometry: Measurements (bounds, pathLength, pointAtLength)
-- | - Path.Transform: Transformations (translate, scale, rotate, reverse)
-- | - Path.Operations: Composition (append, flatten)

module Hydrogen.Schema.Geometry.Path
  ( -- * Re-exports from Types
    module Types
  
    -- * Re-exports from Construction
  , module Construction
  
    -- * Re-exports from Query
  , module Query
  
    -- * Re-exports from Serialization
  , module Serialization
  
    -- * Re-exports from Geometry
  , module Geometry
  
    -- * Re-exports from Transform
  , module Transform
  
    -- * Re-exports from Operations
  , module Operations
  ) where

import Hydrogen.Schema.Geometry.Path.Types
  ( PathCommand(..)
  , allPathCommandTags
  , Path(Path)
  , ArcParams
  , getCommands
  ) as Types

import Hydrogen.Schema.Geometry.Path.Construction
  ( emptyPath
  , pathFromCommands
  , pathFromPoints
  , moveTo
  , lineTo
  , hLineTo
  , vLineTo
  , quadTo
  , smoothQuadTo
  , cubicTo
  , smoothCurveTo
  , arcTo
  , closePath
  ) as Construction

import Hydrogen.Schema.Geometry.Path.Query
  ( isEmpty
  , commandCount
  , isClosed
  , firstPoint
  , lastPoint
  ) as Query

import Hydrogen.Schema.Geometry.Path.Serialization
  ( toSvgString
  , commandToSvgString
  ) as Serialization

import Hydrogen.Schema.Geometry.Path.Geometry
  ( bounds
  , pathLength
  , pointAtLength
  , tangentAtLength
  ) as Geometry

import Hydrogen.Schema.Geometry.Path.Transform
  ( reversePath
  , translatePath
  , scalePath
  , rotatePath
  ) as Transform

import Hydrogen.Schema.Geometry.Path.Operations
  ( appendPath
  , flattenPath
  ) as Operations
