-- |
-- Module      : Lattice.FFI.ThemeState
-- Description : C FFI bindings for theme store pure functions
-- 
-- Exports pure functions from Lattice.State.Theme as C functions
-- for Python/TypeScript interop via JSON serialization
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ThemeState where

import Data.Aeson
  ( decode
  , encode
  , ToJSON(..)
  , Value(..)
  , object
  , (.=)
  )
import qualified Data.ByteString.Lazy as BSL
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String
  ( CString
  , peekCString
  , newCString
  )
import Lattice.State.Theme
  ( themeGradient
  , themePrimary
  , themeSecondary
  , getGlowColor
  , ThemeName(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                 // json // r
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert JSON Value to CString
jsonToCString :: Value -> IO CString
jsonToCString resultJSON = do
  let resultBS = BSL.toStrict (encode resultJSON)
  let resultText = TE.decodeUtf8 resultBS
  newCString (T.unpack resultText)

-- | Create error response JSON
errorResponse :: T.Text -> Value
errorResponse msg = object ["status" .= ("error" :: T.Text), "message" .= msg]

-- | Create success response JSON with result
successResponse :: ToJSON a => a -> Value
successResponse result = object ["status" .= ("success" :: T.Text), "result" .= result]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get theme gradient CSS variable
foreign export ccall "theme_gradient"
  c_theme_gradient :: CString -> IO CString

c_theme_gradient :: CString -> IO CString
c_theme_gradient themeJson = do
  themeStr <- peekCString themeJson
  
  let themeBS = TE.encodeUtf8 (T.pack themeStr)
  
  case decode (BSL.fromStrict themeBS) :: Maybe ThemeName of
    Just theme -> do
      let result = themeGradient theme
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected ThemeName")

-- | Get theme primary CSS variable
foreign export ccall "theme_primary"
  c_theme_primary :: CString -> IO CString

c_theme_primary :: CString -> IO CString
c_theme_primary themeJson = do
  themeStr <- peekCString themeJson
  
  let themeBS = TE.encodeUtf8 (T.pack themeStr)
  
  case decode (BSL.fromStrict themeBS) :: Maybe ThemeName of
    Just theme -> do
      let result = themePrimary theme
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected ThemeName")

-- | Get theme secondary CSS variable
foreign export ccall "theme_secondary"
  c_theme_secondary :: CString -> IO CString

c_theme_secondary :: CString -> IO CString
c_theme_secondary themeJson = do
  themeStr <- peekCString themeJson
  
  let themeBS = TE.encodeUtf8 (T.pack themeStr)
  
  case decode (BSL.fromStrict themeBS) :: Maybe ThemeName of
    Just theme -> do
      let result = themeSecondary theme
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected ThemeName")

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // pure // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Get glow color for theme
foreign export ccall "get_glow_color"
  c_get_glow_color :: CString -> IO CString

c_get_glow_color :: CString -> IO CString
c_get_glow_color themeJson = do
  themeStr <- peekCString themeJson
  
  let themeBS = TE.encodeUtf8 (T.pack themeStr)
  
  case decode (BSL.fromStrict themeBS) :: Maybe ThemeName of
    Just theme -> do
      let result = getGlowColor theme
      jsonToCString (successResponse result)
    Nothing -> jsonToCString (errorResponse "Invalid JSON: expected ThemeName")
