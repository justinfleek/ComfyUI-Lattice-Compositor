-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // qrcode // api
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Component — Pure PureScript QR Code Generation
-- |
-- | ## Design Philosophy
-- |
-- | This is the main public API for QR code generation. It provides:
-- |
-- | 1. **Simple API**: `qrCode content` returns an Element
-- | 2. **Full Control**: `qrCodeWith config content` for customization
-- | 3. **Pure**: No FFI, no effects — pure data transformation
-- | 4. **Deterministic**: Same input = same output = same UUID5
-- |
-- | ## Architecture
-- |
-- | ```
-- | Content → encode → BitStream → interleave → Matrix → render → Element
-- |    ↓
-- | QRContent ADT (URL, Email, WiFi, Calendar, etc.)
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.QRCode as QR
-- |
-- | -- Simple URL
-- | myQR = QR.qrCode (QR.url "https://example.com")
-- |
-- | -- With configuration
-- | styledQR = QR.qrCodeWith
-- |   { errorCorrection: QR.ECHigh
-- |   , style: QR.Dots
-- |   , colors: { dark: "#3b82f6", light: "#ffffff", background: "#ffffff" }
-- |   }
-- |   (QR.url "https://example.com")
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Types (QRVersion, ErrorCorrection, QRMatrix)
-- | - Content/Types (QRContent, content constructors)
-- | - Encoding/* (BitStream, Segment, ReedSolomon)
-- | - Matrix (generateMatrix)
-- | - Render/SVG (renderQRCode)

module Hydrogen.Element.Compound.QRCode.QRCode
  ( -- * Simple API
    qrCode
  , qrCodeWith
  
  -- * Configuration
  , QRConfig
  , defaultConfig
  
  -- * Content Constructors (re-exports)
  , module ContentTypes
  
  -- * Types (re-exports)
  , module Types
  
  -- * Render Config (re-exports)
  , module RenderSVG
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (/=)
  , (==)
  )

import Data.Array (length, foldl, concatMap, index, (..))
import Data.EuclideanRing (div, mod)
import Data.Int.Bits (and, shl)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String.CodeUnits (toCharArray)

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.QRCode.Types
  ( QRVersion
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , QRMatrix
  , EncodingMode
  , mkVersion
  , minVersion
  , getCapacity
  ) as Types
import Hydrogen.Element.Compound.QRCode.Content.Types
  ( QRContent
  , urlContent
  , emailContent
  , phoneContent
  , smsContent
  , wifiContent
  , contentToString
  ) as ContentTypes
import Hydrogen.Element.Compound.QRCode.Encoding.BitStream
  ( BitStream
  , empty
  , append
  , toArray
  , toBytes
  , length
  , addTerminator
  , addPadCodewords
  ) as BitStream
import Hydrogen.Element.Compound.QRCode.Encoding.Segment
  ( encodeString
  , encodeSegments
  , Segment
  , mkSegment
  , detectOptimalMode
  , minVersionForData
  ) as Segment
import Hydrogen.Element.Compound.QRCode.Encoding.ReedSolomon
  ( computeECCodewords
  ) as RS
import Hydrogen.Element.Compound.QRCode.Encoding.Capacity
  ( BlockInfo
  , getBlockInfo
  , totalDataCodewords
  ) as Capacity
import Hydrogen.Element.Compound.QRCode.Matrix
  ( generateMatrix
  ) as Matrix
import Hydrogen.Element.Compound.QRCode.Render.SVG
  ( renderQRCode
  , RenderConfig
  , defaultRenderConfig
  , ModuleStyle(Classic, Rounded, Dots)
  , QRColors
  , defaultColors
  , invertedColors
  ) as RenderSVG

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Full configuration for QR code generation.
type QRConfig =
  { errorCorrection :: Types.ErrorCorrection
  , minVersion :: Maybe Types.QRVersion
  , render :: RenderSVG.RenderConfig
  }

-- | Default configuration.
-- |
-- | - Medium error correction (15% recovery)
-- | - Auto-select minimum version
-- | - Classic square style, black on white
defaultConfig :: QRConfig
defaultConfig =
  { errorCorrection: Types.ECMedium
  , minVersion: Nothing
  , render: RenderSVG.defaultRenderConfig
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // public api
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a QR code Element from content.
-- |
-- | Uses default configuration (medium EC, classic style).
qrCode :: forall msg. ContentTypes.QRContent -> E.Element msg
qrCode content = qrCodeWith defaultConfig content

-- | Generate a QR code Element with custom configuration.
qrCodeWith :: forall msg. QRConfig -> ContentTypes.QRContent -> E.Element msg
qrCodeWith cfg content =
  let
    -- Step 1: Serialize content to string
    dataString = ContentTypes.contentToString content
    
    -- Step 2: Detect optimal encoding mode
    mode = Segment.detectOptimalMode dataString
    
    -- Step 3: Create segment
    segment = Segment.mkSegment mode dataString
    
    -- Step 4: Select version (find minimum that fits)
    version = selectVersionForData cfg dataString
    
    -- Step 5: Encode segment to bitstream
    encodedStream = Segment.encodeString version dataString
    
    -- Step 6: Get data capacity for this version/EC
    blockInfo = Capacity.getBlockInfo cfg.errorCorrection version
    dataCapacity = Capacity.totalDataCodewords blockInfo
    totalBitCapacity = dataCapacity * 8
    
    -- Step 7: Add terminator and padding
    withTerminator = BitStream.addTerminator totalBitCapacity encodedStream
    paddedStream = BitStream.addPadCodewords totalBitCapacity withTerminator
    
    -- Step 8: Get data codewords (as bytes) and generate EC
    dataCodewords = BitStream.toBytes paddedStream
    codewords = generateCodewords cfg.errorCorrection version dataCodewords
    
    -- Step 9: Convert to bit array
    dataBits = codewordsToBits codewords
    
    -- Step 10: Generate matrix
    matrix = Matrix.generateMatrix version cfg.errorCorrection dataBits
    
    -- Step 11: Render to SVG
    element = RenderSVG.renderQRCode cfg.render matrix
  in
    element

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // internal generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select appropriate QR version for data.
selectVersionForData :: QRConfig -> String -> Types.QRVersion
selectVersionForData cfg dataString =
  case cfg.minVersion of
    Just v -> v
    Nothing -> fromMaybe Types.minVersion (Segment.minVersionForData cfg.errorCorrection dataString)

-- | Generate data and error correction codewords.
generateCodewords :: Types.ErrorCorrection -> Types.QRVersion -> Array Int -> Array Int
generateCodewords ec version dataCodewords =
  let
    -- Get block structure for this version/EC (complete ISO 18004 table)
    blockInfo = Capacity.getBlockInfo ec version
    
    -- Generate error correction for each block
    blocks = splitIntoBlocks dataCodewords blockInfo
    
    -- Add EC to each block
    blocksWithEC = map (addErrorCorrection blockInfo.ecPerBlock) blocks
    
    -- Interleave blocks
    interleaved = interleaveBlocks blocksWithEC blockInfo
  in
    interleaved

-- | Split data into blocks.
splitIntoBlocks :: Array Int -> Capacity.BlockInfo -> Array (Array Int)
splitIntoBlocks codewords info =
  let
    -- Group 1 blocks
    group1 = splitN info.group1Data info.group1Blocks codewords 0
    -- Group 2 blocks (if any)
    offset = info.group1Blocks * info.group1Data
    group2 = splitN info.group2Data info.group2Blocks codewords offset
  in
    group1.blocks <> group2.blocks
  where
    splitN :: Int -> Int -> Array Int -> Int -> { blocks :: Array (Array Int), offset :: Int }
    splitN size count arr startOffset =
      foldl (\acc _ ->
        let
          block = takeSlice acc.offset size arr
        in
          { blocks: acc.blocks <> [block], offset: acc.offset + size }
      ) { blocks: [], offset: startOffset } (0 .. (count - 1))
    
    takeSlice :: Int -> Int -> Array Int -> Array Int
    takeSlice offset size arr =
      foldl (\acc i ->
        case arrayIndex (offset + i) arr of
          Just v -> acc <> [v]
          Nothing -> acc <> [0]
      ) [] (0 .. (size - 1))

-- | Add error correction to a data block.
addErrorCorrection :: Int -> Array Int -> { data :: Array Int, ec :: Array Int }
addErrorCorrection ecCount dataBlock =
  let
    ec = RS.computeECCodewords dataBlock ecCount
  in
    { data: dataBlock, ec: ec }

-- | Interleave blocks for final codeword sequence.
interleaveBlocks :: Array { data :: Array Int, ec :: Array Int } -> Capacity.BlockInfo -> Array Int
interleaveBlocks blocks info =
  let
    -- Interleave data codewords
    maxDataLen = foldl (\m b -> let l = length b.data in if l >= m then l else m) 0 blocks
    interleavedData = interleaveArrays (map (\b -> b.data) blocks) maxDataLen
    
    -- Interleave EC codewords
    interleavedEC = interleaveArrays (map (\b -> b.ec) blocks) info.ecPerBlock
  in
    interleavedData <> interleavedEC
  where
    interleaveArrays :: Array (Array Int) -> Int -> Array Int
    interleaveArrays arrs maxLen =
      concatMap (\i -> 
        concatMap (\arr -> 
          case arrayIndex i arr of
            Just v -> [v]
            Nothing -> []
        ) arrs
      ) (0 .. (maxLen - 1))

-- | Convert codewords to bit array.
codewordsToBits :: Array Int -> Array Int
codewordsToBits codewords =
  concatMap codewordToBits codewords
  where
    codewordToBits :: Int -> Array Int
    codewordToBits cw =
      map (\i -> if testBit cw (7 - i) then 1 else 0) (0 .. 7)
    
    testBit :: Int -> Int -> Boolean
    testBit n bit =
      let mask = shl 1 bit
      in and n mask /= 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safe array index (wrapper for Data.Array.index with flipped args).
arrayIndex :: forall a. Int -> Array a -> Maybe a
arrayIndex i arr = index arr i
