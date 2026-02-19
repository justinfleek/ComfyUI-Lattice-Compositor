-- |
-- Module      : Lattice.FFI.SVGPathParsing
-- Description : C FFI exports for SVGPathParsing service
-- 
-- Exports Haskell functions as C-compatible functions for Python interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.SVGPathParsing where

import Foreign.C.Types (CInt(..))
import Foreign.C.String (CString, peekCString, newCString)
import Foreign.Ptr (Ptr)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import Data.Aeson (Value(..), object, (.=), encode, ToJSON(..))
import Data.Aeson.Key (fromText)

import Lattice.Services.SVGPathParsing
  ( parseSVGToPaths
  , parsePathData
  , ParsedPath(..)
  , ControlPoint(..)
  , ControlPointHandle(..)
  , ControlPointType(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // json // instances // for // ffi
-- ════════════════════════════════════════════════════════════════════════════

instance ToJSON ControlPointHandle where
  toJSON (ControlPointHandle x y) = object
    [ fromText "x" .= x
    , fromText "y" .= y
    ]

instance ToJSON ControlPointType where
  toJSON CornerPoint = String (T.pack "corner")
  toJSON SmoothPoint = String (T.pack "smooth")

instance ToJSON ControlPoint where
  toJSON (ControlPoint id_ x y mInHandle mOutHandle typ) = object
    [ fromText "id" .= id_
    , fromText "x" .= x
    , fromText "y" .= y
    , fromText "inHandle" .= mInHandle
    , fromText "outHandle" .= mOutHandle
    , fromText "type" .= typ
    ]

instance ToJSON ParsedPath where
  toJSON (ParsedPath id_ fill stroke controlPoints closed) = object
    [ fromText "id" .= id_
    , fromText "fill" .= fill
    , fromText "stroke" .= stroke
    , fromText "controlPoints" .= controlPoints
    , fromText "closed" .= closed
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // parsing // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Export parseSVGToPaths as C function
-- C signature: char* parse_svg_to_paths(char* svg_string, int img_width, int img_height)
-- Returns: JSON array of parsed paths
-- Memory: Caller must free the returned CString using free()
foreign export ccall "parse_svg_to_paths"
  c_parse_svg_to_paths :: CString -> CInt -> CInt -> IO CString

c_parse_svg_to_paths :: CString -> CInt -> CInt -> IO CString
c_parse_svg_to_paths svgPtr (CInt imgWidth) (CInt imgHeight) = do
  svgStr <- peekCString svgPtr
  let svgText = T.pack svgStr
  
  -- Parse SVG
  let paths = parseSVGToPaths svgText (fromIntegral imgWidth) (fromIntegral imgHeight)
  
  -- Convert to JSON
  let result = object
        [ fromText "status" .= (T.pack "success")
        , fromText "paths" .= paths
        ]
  let resultBS = BSL.toStrict (encode result)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- | Export parsePathData as C function
-- C signature: char* parse_path_data(char* path_data, int path_idx)
-- Returns: JSON with control points and closed flag
-- Memory: Caller must free the returned CString using free()
foreign export ccall "parse_path_data"
  c_parse_path_data :: CString -> CInt -> IO CString

c_parse_path_data :: CString -> CInt -> IO CString
c_parse_path_data pathDataPtr (CInt pathIdx) = do
  pathDataStr <- peekCString pathDataPtr
  let pathDataText = T.pack pathDataStr
  
  -- Parse path data
  let (controlPoints, closed) = parsePathData pathDataText (fromIntegral pathIdx)
  
  -- Convert to JSON
  let result = object
        [ fromText "status" .= (T.pack "success")
        , fromText "controlPoints" .= controlPoints
        , fromText "closed" .= closed
        ]
  let resultBS = BSL.toStrict (encode result)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)
