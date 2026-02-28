-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // ui // playhead-button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayheadButton — Media Playback Control Button
-- |
-- | Specialized button for video/audio playback controls.

module Hydrogen.UI.PlayheadButton
  ( -- * Components
    play
  , pause
  , stop
  , skipForward
  , skipBackward
  , fastForward
  , rewind
  , nextTrack
  , previousTrack
  , mute
  , unmute
  , volumeUp
  , volumeDown
  , volumeSlider
  , scrubber
  , timeDisplay
  , fullscreen
  , exitFullscreen
  , pictureInPicture
  , closedCaptions
  , settings
  , record
  , live
  , mediaButton

  -- * Configuration
  , PlayheadConfig
  , defaultConfig

  -- * Config Modifiers
  , size
  , variant
  , disabled
  , loading
  , compact
  , className
  , id_
  , onClick
  , tabIndex
  , ariaLabel
  , title

  -- * Playback State
  , playbackState
  , PlaybackState(..)

  -- * Time Format
  , TimeFormat(..)

  -- * Progress & Position
  , progress
  , buffered
  , currentTime
  , duration
  , showTime
  , timeFormat

  -- * Scrubber Options
  , scrubber
  , thumbSize
  , trackHeight
  , progressColor

  -- * Volume
  , volume
  , volumeMuted

  -- * Visual Options
  , showProgress
  , glow
  , pulse
  , sizePixels

  -- * Sizes
  , PlayheadSize(..)

  -- * Variants
  , PlayheadVariant(..)
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (/=)
  , (<>)
  , (&&)
  , (||)
  , ($)
  , (>)
  , (<)
  , (-)
  , (*)
  , (/)
  , (>>>)
  , mod
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Unit (Unit, unit)

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // sizes
-- ═════════════════════════════════════════════════════════════════════════════

data PlayheadSize
  = Xs
  | Sm
  | Md
  | Lg
  | Xl
  | Pixel Int

derive instance eqPlayheadSize :: Eq PlayheadSize

-- ═════════════════════════════════════════════════════════════════════════════

data PlayheadVariant
  = Default
  | Minimal
  | Filled
  | Outlined
  | Ghost

derive instance eqPlayheadVariant :: Eq PlayheadVariant

-- ═════════════════════════════════════════════════════════════════════════════

data PlaybackState
  = Playing
  | Paused
  | Stopped
  | Buffering
  | Seeking
  | Loading

derive instance eqPlaybackState :: Eq PlaybackState

data TimeFormat
  = Compact
  | Full
  | Seconds

derive instance eqTimeFormat :: Eq TimeFormat

-- ═════════════════════════════════════════════════════════════════════════════

type PlayheadConfig msg =
  { size :: PlayheadSize
  , variant :: PlayheadVariant
  , disabled :: Boolean
  , loading :: Boolean
  , compact :: Boolean
  , className :: String
  , id_ :: Maybe String
  , onClick :: Maybe msg
  , tabIndex :: Maybe Int
  , ariaLabel :: Maybe String
  , title :: Maybe String
  , playbackState :: PlaybackState
  , progress :: Number
  , buffered :: Maybe Number
  , currentTime :: Maybe Number
  , duration :: Maybe Number
  , showTime :: Boolean
  , timeFormat :: TimeFormat
  , showTimeRemaining :: Boolean
  , isScrubber :: Boolean
  , thumbSize :: PlayheadSize
  , trackHeight :: Maybe String
  , progressColor :: Maybe String
  , showThumb :: Boolean
  , volume :: Number
  , volumeMuted :: Boolean
  , showProgress :: Boolean
  , glow :: Boolean
  , pulse :: Boolean
  , sizePixels :: Maybe String
  }

defaultConfig :: forall msg. PlayheadConfig msg
defaultConfig =
  { size: Md
  , variant: Default
  , disabled: false
  , loading: false
  , compact: false
  , className: ""
  , id_: Nothing
  , onClick: Nothing
  , tabIndex: Nothing
  , ariaLabel: Nothing
  , title: Nothing
  , playbackState: Paused
  , progress: 0.0
  , buffered: Nothing
  , currentTime: Nothing
  , duration: Nothing
  , showTime: false
  , timeFormat: Compact
  , showTimeRemaining: false
  , isScrubber: false
  , thumbSize: Md
  , trackHeight: Nothing
  , progressColor: Nothing
  , showThumb: true
  , volume: 1.0
  , volumeMuted: false
  , showProgress: false
  , glow: false
  , pulse: false
  , sizePixels: Nothing
  }

type ConfigMod msg = PlayheadConfig msg -> PlayheadConfig msg

-- ═════════════════════════════════════════════════════════════════════════════

size :: forall msg. PlayheadSize -> ConfigMod msg
size s config = config { size = s }

variant :: forall msg. PlayheadVariant -> ConfigMod msg
variant v config = config { variant = v }

disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

loading :: forall msg. Boolean -> ConfigMod msg
loading l config = config { loading = l }

compact :: forall msg. Boolean -> ConfigMod msg
compact c config = config { compact = c }

className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

id_ :: forall msg. String -> ConfigMod msg
id_ i config = config { id_ = Just i }

onClick :: forall msg. msg -> ConfigMod msg
onClick msg config = config { onClick = Just msg }

tabIndex :: forall msg. Int -> ConfigMod msg
tabIndex ti config = config { tabIndex = Just ti }

ariaLabel :: forall msg. String -> ConfigMod msg
ariaLabel al config = config { ariaLabel = Just al }

title :: forall msg. String -> ConfigMod msg
title t config = config { title = Just t }

playbackState :: forall msg. PlaybackState -> ConfigMod msg
playbackState ps config = config { playbackState = ps }

progress :: forall msg. Number -> ConfigMod msg
progress p config = config { progress = clamp01 p }
  where
  clamp01 n = if n < 0.0 then 0.0 else if n > 1.0 then 1.0 else n

buffered :: forall msg. Number -> ConfigMod msg
buffered b config = config { buffered = Just (clamp01 b) }
  where
  clamp01 n = if n < 0.0 then 0.0 else if n > 1.0 then 1.0 else n

currentTime :: forall msg. Number -> ConfigMod msg
currentTime t config = config { currentTime = Just t }

duration :: forall msg. Number -> ConfigMod msg
duration d config = config { duration = Just d }

showTime :: forall msg. Boolean -> ConfigMod msg
showTime st config = config { showTime = st }

timeFormat :: forall msg. TimeFormat -> ConfigMod msg
timeFormat tf config = config { timeFormat = tf }

thumbSize :: forall msg. PlayheadSize -> ConfigMod msg
thumbSize ts config = config { thumbSize = ts }

trackHeight :: forall msg. String -> ConfigMod msg
trackHeight th config = config { trackHeight = Just th }

progressColor :: forall msg. String -> ConfigMod msg
progressColor pc config = config { progressColor = Just pc }

volume :: forall msg. Number -> ConfigMod msg
volume v config = config { volume = clamp01 v }
  where
  clamp01 n = if n < 0.0 then 0.0 else if n > 1.0 then 1.0 else n

volumeMuted :: forall msg. Boolean -> ConfigMod msg
volumeMuted vm config = config { volumeMuted = vm }

showProgress :: forall msg. Boolean -> ConfigMod msg
showProgress sp config = config { showProgress = sp }

glow :: forall msg. Boolean -> ConfigMod msg
glow g config = config { glow = g }

pulse :: forall msg. Boolean -> ConfigMod msg
pulse p config = config { pulse = p }

sizePixels :: forall msg. String -> ConfigMod msg
sizePixels sp config = config { sizePixels = Just sp }

-- ═════════════════════════════════════════════════════════════════════════════

sizeClasses :: PlayheadSize -> String
sizeClasses = case _ of
  Xs -> "w-6 h-6 text-xs"
  Sm -> "w-8 h-8 text-sm"
  Md -> "w-10 h-10 text-base"
  Lg -> "w-12 h-12 text-lg"
  Xl -> "w-16 h-16 text-xl"
  Pixel n -> "w-" <> show n <> " h-" <> show n

variantClasses :: PlayheadVariant -> String
variantClasses = case _ of
  Default -> "bg-gray-800/90 text-white hover:bg-gray-700"
  Minimal -> "bg-transparent text-gray-300 hover:text-white"
  Filled -> "bg-white text-gray-900 hover:bg-gray-100"
  Outlined -> "bg-transparent border-2 border-white/30 text-white hover:border-white"
  Ghost -> "bg-transparent text-gray-400 hover:bg-white/10 hover:text-white"

-- ═════════════════════════════════════════════════════════════════════════════

play :: forall msg. Array (ConfigMod msg) -> E.Element msg
play mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "▶"

pause :: forall msg. Array (ConfigMod msg) -> E.Element msg
pause mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏸"

stop :: forall msg. Array (ConfigMod msg) -> E.Element msg
stop mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏹"

skipForward :: forall msg. Array (ConfigMod msg) -> E.Element msg
skipForward mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏭"

skipBackward :: forall msg. Array (ConfigMod msg) -> E.Element msg
skipBackward mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏮"

fastForward :: forall msg. Array (ConfigMod msg) -> E.Element msg
fastForward mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏩"

rewind :: forall msg. Array (ConfigMod msg) -> E.Element msg
rewind mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏪"

nextTrack :: forall msg. Array (ConfigMod msg) -> E.Element msg
nextTrack mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏭"

previousTrack :: forall msg. Array (ConfigMod msg) -> E.Element msg
previousTrack mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏮"

mute :: forall msg. Array (ConfigMod msg) -> E.Element msg
mute mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "🔇"

unmute :: forall msg. Array (ConfigMod msg) -> E.Element msg
unmute mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "🔊"

volumeUp :: forall msg. Array (ConfigMod msg) -> E.Element msg
volumeUp mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "🔊"

volumeDown :: forall msg. Array (ConfigMod msg) -> E.Element msg
volumeDown mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "🔉"

fullscreen :: forall msg. Array (ConfigMod msg) -> E.Element msg
fullscreen mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⛶"

exitFullscreen :: forall msg. Array (ConfigMod msg) -> E.Element msg
exitFullscreen mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⛶"

pictureInPicture :: forall msg. Array (ConfigMod msg) -> E.Element msg
pictureInPicture mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "📺"

closedCaptions :: forall msg. Array (ConfigMod msg) -> E.Element msg
closedCaptions mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "📝"

settings :: forall msg. Array (ConfigMod msg) -> E.Element msg
settings mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⚙"

record :: forall msg. Array (ConfigMod msg) -> E.Element msg
record mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "⏺"

live :: forall msg. Array (ConfigMod msg) -> E.Element msg
live mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) "🔴"

mediaButton :: forall msg. String -> Array (ConfigMod msg) -> E.Element msg
mediaButton icon mods = buildMediaButton (foldl (\c f -> f c) defaultConfig mods) icon

-- ═════════════════════════════════════════════════════════════════════════════

volumeSlider :: forall msg. Array (ConfigMod msg) -> E.Element msg
volumeSlider mods =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    size = sizeClasses config.size
    icon = if config.volumeMuted || config.volume == 0.0 then "🔇" else "🔊"
    progressWidth = show (config.volume * 100.0) <> "%"
  in
    E.div_ [ E.class_ "flex items-center gap-2" ]
      [ E.button_ [ E.class_ size ] [ E.text icon ]
      , E.div_ [ E.class_ "w-20 h-1 bg-white/30 rounded-full relative" ]
        [ E.div_ [ E.class_ "bg-white h-full rounded-full absolute left-0 top-0"
                  , E.style "width" progressWidth
                 ] []
        ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════

scrubber :: forall msg. Array (ConfigMod msg) -> E.Element msg
scrubber mods =
  let
    config = foldl (\c f -> f c) (defaultConfig { isScrubber = true }) mods
    progressWidth = show (config.progress * 100.0) <> "%"
    bufferedWidth = case config.buffered of
      Just b -> show (b * 100.0) <> "%"
      Nothing -> progressWidth
    trackH = fromMaybe "h-1" config.trackHeight
    progressBg = fromMaybe "bg-blue-500" config.progressColor
  in
    E.div_ 
      [ E.class_ ("w-full " <> trackH <> " cursor-pointer relative")
      , E.role "slider"
      ]
      [ E.div_ [ E.class_ "bg-white/20 w-full h-full rounded-full" ] []
      , E.div_ [ E.class_ "bg-white/30 absolute h-full top-0 left-0 rounded-full"
                , E.style "width" bufferedWidth
                ] []
      , E.div_ [ E.class_ (progressBg <> " absolute h-full top-0 left-0 rounded-full")
                , E.style "width" progressWidth
                ] []
      ]

-- ═════════════════════════════════════════════════════════════════════════════

timeDisplay :: forall msg. Array (ConfigMod msg) -> E.Element msg
timeDisplay mods =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    timeStr = case config.currentTime of
      Just t -> formatTime t
      Nothing -> "0:00"
    durationStr = case config.duration of
      Just d -> " / " <> formatTime d
      Nothing -> ""
  in
    E.span_ 
      [ E.class_ "font-mono text-sm text-white/90" 
      ] 
      [ E.text (timeStr <> durationStr) ]

formatTime :: Number -> String
formatTime seconds = show seconds

-- ═════════════════════════════════════════════════════════════════════════════

buildMediaButton :: forall msg. PlayheadConfig msg -> String -> E.Element msg
buildMediaButton config iconChar =
  let
    size = sizeClasses config.size
    variant = variantClasses config.variant
    
    base = "inline-flex items-center justify-center rounded-full transition-all duration-150 focus:outline-none disabled:pointer-events-none disabled:opacity-50"
    
    sc = if config.disabled then "" else variant
    ac = if config.disabled then "" else "active:scale-95"
    hc = if config.disabled then "" else "hover:scale-105"
    gc = if config.glow then "shadow-lg shadow-blue-500/50" else ""
    pc = if config.pulse then "animate-pulse" else ""
    customSize = fromMaybe "" config.sizePixels
    loadingClass = if config.loading then "animate-pulse" else ""
    
    allClasses = base <> " " <> sc <> " " <> ac <> " " <> hc 
      <> " " <> gc <> " " <> pc <> " " <> loadingClass
      <> " " <> size <> " " <> config.className
      <> if customSize /= "" then " " <> customSize else ""
    
    attrs = 
      [ E.class_ allClasses
      , E.type_ "button"
      , E.disabled config.disabled
      ]
      <> case config.id_ of
          Just id -> [ E.id_ id ]
          Nothing -> []
      <> case config.tabIndex of
          Just ti -> [ E.tabIndex ti ]
          Nothing -> []
      <> case config.title of
          Just t -> [ E.title t ]
          Nothing -> []
      <> case config.ariaLabel of
          Just al -> [ E.ariaLabel al ]
          Nothing -> []
      <> case config.onClick of
          Just msg -> [ E.onClick msg ]
          Nothing -> []
  in
    E.button_ attrs [ E.text iconChar ]
