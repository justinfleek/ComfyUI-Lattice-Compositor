-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // qrcode // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Types — Core data structures for QR code generation.
-- |
-- | ## Design Philosophy
-- |
-- | QR codes are deterministic: given input + error correction + version,
-- | the output matrix is a pure function. No FFI needed.
-- |
-- | ## Module Structure
-- |
-- | This is the orchestrator module that re-exports:
-- | - Types.Version: QRVersion (1-40, determines size)
-- | - Types.ErrorCorrection: Error correction levels (L/M/Q/H)
-- | - Types.EncodingMode: Encoding modes (Numeric/Alphanumeric/Byte/Kanji)
-- | - Types.Module: Module and ModuleType (individual cells)
-- | - Types.Matrix: QRMatrix (2D grid of modules)
-- | - Types.Capacity: Character capacity lookup
-- | - Types.Codeword: 8-bit data values
-- |
-- | ## QR Code Structure (ISO/IEC 18004)
-- |
-- | ```
-- | ┌─────────────────────────────┐
-- | │ ▓▓▓▓▓▓▓ ░ ░░░░░ ░ ▓▓▓▓▓▓▓ │  Finder patterns (3 corners)
-- | │ ▓░░░░░▓ ░ ░░░░░ ░ ▓░░░░░▓ │
-- | │ ▓░▓▓▓░▓ ░ ░░░░░ ░ ▓░▓▓▓░▓ │
-- | │ ▓░▓▓▓░▓ ░ ░░░░░ ░ ▓░▓▓▓░▓ │
-- | │ ▓░▓▓▓░▓ ░ ░░░░░ ░ ▓░▓▓▓░▓ │
-- | │ ▓░░░░░▓ ░ ░░░░░ ░ ▓░░░░░▓ │
-- | │ ▓▓▓▓▓▓▓ ░ ▓ ░ ▓ ░ ▓▓▓▓▓▓▓ │  Timing patterns (alternating)
-- | │ ░░░░░░░ ░ ░░░░░ ░ ░░░░░░░ │  Separator (white quiet zone)
-- | │ ░░░░░░░░░░ DATA ░░░░░░░░░ │  Data + Error correction
-- | │ ...                   ... │
-- | └─────────────────────────────┘
-- | ```

module Hydrogen.Element.Compound.QRCode.Types
  ( -- * Version (re-exported)
    module Version
  
  -- * Error Correction (re-exported)
  , module ErrorCorrection
  
  -- * Encoding Mode (re-exported)
  , module EncodingMode
  
  -- * Module (re-exported)
  , module Module
  
  -- * QR Matrix (re-exported)
  , module Matrix
  
  -- * Capacity (re-exported)
  , module Capacity
  
  -- * Codeword (re-exported)
  , module Codeword
  ) where

-- Re-exported modules
import Hydrogen.Element.Compound.QRCode.Types.Version
  ( QRVersion(QRVersion)
  , mkVersion
  , versionToInt
  , minVersion
  , maxVersion
  , versionSize
  ) as Version

import Hydrogen.Element.Compound.QRCode.Types.ErrorCorrection
  ( ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , ecToString
  , ecRecoveryPercent
  ) as ErrorCorrection

import Hydrogen.Element.Compound.QRCode.Types.EncodingMode
  ( EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  , modeIndicator
  , detectMode
  ) as EncodingMode

import Hydrogen.Element.Compound.QRCode.Types.Module
  ( Module(Dark, Light, Reserved)
  , ModuleType(DataModule, FinderModule, TimingModule, AlignmentModule, FormatModule, VersionModule, QuietModule)
  , isDark
  , isLight
  , isReserved
  ) as Module

import Hydrogen.Element.Compound.QRCode.Types.Matrix
  ( QRMatrix
  , mkMatrix
  , matrixSize
  , getModule
  , setModule
  , rowToArray
  , toNestedArray
  ) as Matrix

import Hydrogen.Element.Compound.QRCode.Types.Capacity
  ( Capacity
  , getCapacity
  ) as Capacity

import Hydrogen.Element.Compound.QRCode.Types.Codeword
  ( Codeword(Codeword)
  , mkCodeword
  , codewordValue
  , minCodeword
  , maxCodeword
  ) as Codeword
