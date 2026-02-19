-- |
-- Module      : Lattice.FFI.ThemeGeneratorFFI
-- Description : FFI bindings for theme generation from VSCode extension
-- 
-- Exports functions for generating base16 themes with user-selected colors
-- and monitor-specific black balance
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.ThemeGeneratorFFI
  ( generateThemeFFI
  , generateThemeVariantsFFI
  ) where

import Foreign.C.String (CString, newCString, peekCString)
import Foreign.C.Types (CDouble, CInt)
import Foreign.Marshal.Alloc (free)
import Foreign.Ptr (Ptr)
import Data.Aeson (encode, decode, Value)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Map.Strict as Map
import Lattice.Utils.BlackBalance
  ( MonitorType(..)
  , BaseColor(..)
  , HeroColor(..)
  , ThemeConfig(..)
  , ThemeVariant(..)
  , generateThemeVariants
  , generateLightThemeVariants
  )
import Lattice.Utils.Base16Theme
  ( Base16Palette(..)
  , generateBase16Theme
  , paletteToHex
  )
import Lattice.Types.Color
  ( Hue(..)
  , Saturation(..)
  , Lightness(..)
  , validateHue
  , validateSaturation
  , validateLightness
  , rgbToHex
  , hueValue
  , lightnessValue
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // json // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Convert JSON string to ThemeConfig
parseThemeConfig :: T.Text -> Maybe ThemeConfig
parseThemeConfig jsonText =
  case decode (BL.fromStrict (TE.encodeUtf8 jsonText)) of
    Just (config :: ThemeConfig) -> Just config
    Nothing -> Nothing

-- | Convert ThemeVariant list to JSON
themeVariantsToJSON :: [ThemeVariant] -> T.Text
themeVariantsToJSON variants =
  TE.decodeUtf8 (BL.toStrict (encode variants))

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // theme // generation
-- ════════════════════════════════════════════════════════════════════════════

-- | Generate base16 theme from user configuration
generateThemeFromConfig :: ThemeConfig -> Base16Palette
generateThemeFromConfig config =
  let backgroundL = lightnessValue (configBlackBalance config)
      -- Use hero color hue for accent colors
      heroH = hueValue (heroHue (configHeroColor config))
      -- Generate theme with adjusted background lightness
      theme = generateBase16Theme backgroundL
  in theme

-- | Generate all theme variants from configuration
generateAllVariants :: ThemeConfig -> [ThemeVariant]
generateAllVariants config =
  let variants = if not (configMode config)
        then generateThemeVariants config
        else generateLightThemeVariants config
      -- Convert each variant to Base16Palette and populate colors
      convertVariant (ThemeVariant name bgL _) =
        let palette = generateBase16Theme (lightnessValue bgL)
            colorPairs = paletteToHex palette
            -- Convert list of (Text, Text) pairs to Map
            colorMap = Map.fromList colorPairs
        in ThemeVariant
          { variantName = name
          , variantBackgroundLightness = bgL
          , variantColors = colorMap
          }
  in map convertVariant variants

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // ffi // exports
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Generate theme variants from JSON config
-- Input: JSON string with ThemeConfig
-- Output: JSON string with ThemeVariant list
foreign export ccall generateThemeVariantsFFI :: CString -> IO CString

generateThemeVariantsFFI :: CString -> IO CString
generateThemeVariantsFFI jsonCStr = do
  jsonText <- peekCString jsonCStr
  case parseThemeConfig (T.pack jsonText) of
    Just config -> do
      let variants = generateAllVariants config
          jsonOutput = themeVariantsToJSON variants
      newCString (T.unpack jsonOutput)
    Nothing -> do
      -- Return error JSON
      newCString "{\"error\": \"Invalid theme config\"}"

-- | FFI: Generate single theme from JSON config
foreign export ccall generateThemeFFI :: CString -> IO CString

generateThemeFFI :: CString -> IO CString
generateThemeFFI jsonCStr = do
  jsonText <- peekCString jsonCStr
  case parseThemeConfig (T.pack jsonText) of
    Just config -> do
      let theme = generateThemeFromConfig config
          colors = paletteToHex theme
          jsonOutput = TE.decodeUtf8 (BL.toStrict (encode colors))
      newCString (T.unpack jsonOutput)
    Nothing -> do
      newCString "{\"error\": \"Invalid theme config\"}"
