-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // util // media-query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Responsive media query utilities
-- |
-- | Type-safe wrappers around the matchMedia API for responsive design.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.MediaQuery as MQ
-- |
-- | -- Check current breakpoint
-- | isMobile <- MQ.isMobile
-- | isDesktop <- MQ.isDesktop
-- |
-- | -- Listen for changes
-- | unsubscribe <- MQ.onMediaChange "(min-width: 768px)" \matches ->
-- |   if matches
-- |     then Console.log "Now on tablet or larger"
-- |     else Console.log "Now on mobile"
-- |
-- | -- Detect user preferences
-- | prefersDark <- MQ.prefersDarkMode
-- | reducedMotion <- MQ.prefersReducedMotion
-- |
-- | -- Orientation
-- | isLandscape <- MQ.isLandscape
-- | ```
module Hydrogen.Util.MediaQuery
  ( -- * Core Query
    matchMedia
  , onMediaChange
    -- * Breakpoint Helpers
  , isMobile
  , isTablet
  , isDesktop
  , isLargeDesktop
    -- * Breakpoint Listeners
  , onBreakpointChange
  , Breakpoint(..)
  , currentBreakpoint
    -- * User Preferences
  , prefersDarkMode
  , prefersLightMode
  , prefersReducedMotion
  , prefersReducedTransparency
  , prefersContrast
  , onColorSchemeChange
    -- * Orientation
  , isPortrait
  , isLandscape
  , onOrientationChange
    -- * Display Features
  , isHighDPI
  , isTouch
  , isPrint
  ) where

import Prelude


import Effect (Effect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import matchMediaImpl :: String -> Effect Boolean

foreign import onMediaChangeImpl 
  :: String 
  -> (Boolean -> Effect Unit) 
  -> Effect (Effect Unit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a media query matches
-- |
-- | ```purescript
-- | matches <- matchMedia "(min-width: 768px)"
-- | ```
matchMedia :: String -> Effect Boolean
matchMedia = matchMediaImpl

-- | Listen for media query changes
-- |
-- | Returns an unsubscribe function.
-- |
-- | ```purescript
-- | unsubscribe <- onMediaChange "(prefers-color-scheme: dark)" \isDark ->
-- |   applyTheme (if isDark then Dark else Light)
-- | ```
onMediaChange :: String -> (Boolean -> Effect Unit) -> Effect (Effect Unit)
onMediaChange = onMediaChangeImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // breakpoint helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard breakpoints (following Tailwind conventions)
-- | sm: 640px, md: 768px, lg: 1024px, xl: 1280px, 2xl: 1536px

-- | Check if viewport is mobile (< 768px)
isMobile :: Effect Boolean
isMobile = not <$> matchMedia "(min-width: 768px)"

-- | Check if viewport is tablet (>= 768px and < 1024px)
isTablet :: Effect Boolean
isTablet = do
  above768 <- matchMedia "(min-width: 768px)"
  below1024 <- not <$> matchMedia "(min-width: 1024px)"
  pure $ above768 && below1024

-- | Check if viewport is desktop (>= 1024px)
isDesktop :: Effect Boolean
isDesktop = matchMedia "(min-width: 1024px)"

-- | Check if viewport is large desktop (>= 1280px)
isLargeDesktop :: Effect Boolean
isLargeDesktop = matchMedia "(min-width: 1280px)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // breakpoint listeners
-- ═════════════════════════════════════════════════════════════════════════════

-- | Breakpoint enumeration
data Breakpoint
  = Mobile      -- < 768px
  | Tablet      -- >= 768px and < 1024px
  | Desktop     -- >= 1024px and < 1280px
  | LargeDesktop -- >= 1280px

derive instance eqBreakpoint :: Eq Breakpoint
derive instance ordBreakpoint :: Ord Breakpoint

instance showBreakpoint :: Show Breakpoint where
  show Mobile = "Mobile"
  show Tablet = "Tablet"
  show Desktop = "Desktop"
  show LargeDesktop = "LargeDesktop"

-- | Get the current breakpoint
currentBreakpoint :: Effect Breakpoint
currentBreakpoint = do
  xl <- matchMedia "(min-width: 1280px)"
  lg <- matchMedia "(min-width: 1024px)"
  md <- matchMedia "(min-width: 768px)"
  pure $
    if xl then LargeDesktop
    else if lg then Desktop
    else if md then Tablet
    else Mobile

-- | Listen for breakpoint changes
-- |
-- | ```purescript
-- | unsubscribe <- onBreakpointChange \bp ->
-- |   case bp of
-- |     Mobile -> enableMobileNav
-- |     _ -> enableDesktopNav
-- | ```
onBreakpointChange :: (Breakpoint -> Effect Unit) -> Effect (Effect Unit)
onBreakpointChange callback = do
  -- Subscribe to each breakpoint transition
  unsub1 <- onMediaChange "(min-width: 768px)" \_ -> do
    bp <- currentBreakpoint
    callback bp
  unsub2 <- onMediaChange "(min-width: 1024px)" \_ -> do
    bp <- currentBreakpoint
    callback bp
  unsub3 <- onMediaChange "(min-width: 1280px)" \_ -> do
    bp <- currentBreakpoint
    callback bp
  
  pure do
    unsub1
    unsub2
    unsub3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // user preferences
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if user prefers dark color scheme
prefersDarkMode :: Effect Boolean
prefersDarkMode = matchMedia "(prefers-color-scheme: dark)"

-- | Check if user prefers light color scheme
prefersLightMode :: Effect Boolean
prefersLightMode = matchMedia "(prefers-color-scheme: light)"

-- | Check if user prefers reduced motion
-- |
-- | Important for accessibility - disable animations when true.
prefersReducedMotion :: Effect Boolean
prefersReducedMotion = matchMedia "(prefers-reduced-motion: reduce)"

-- | Check if user prefers reduced transparency
prefersReducedTransparency :: Effect Boolean
prefersReducedTransparency = matchMedia "(prefers-reduced-transparency: reduce)"

-- | Check if user prefers high contrast
prefersContrast :: Effect Boolean
prefersContrast = matchMedia "(prefers-contrast: more)"

-- | Listen for color scheme changes
-- |
-- | ```purescript
-- | unsubscribe <- onColorSchemeChange \isDark ->
-- |   if isDark then applyDarkTheme else applyLightTheme
-- | ```
onColorSchemeChange :: (Boolean -> Effect Unit) -> Effect (Effect Unit)
onColorSchemeChange = onMediaChange "(prefers-color-scheme: dark)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if device is in portrait orientation
isPortrait :: Effect Boolean
isPortrait = matchMedia "(orientation: portrait)"

-- | Check if device is in landscape orientation
isLandscape :: Effect Boolean
isLandscape = matchMedia "(orientation: landscape)"

-- | Listen for orientation changes
-- |
-- | Callback receives `true` for portrait, `false` for landscape.
onOrientationChange :: (Boolean -> Effect Unit) -> Effect (Effect Unit)
onOrientationChange = onMediaChange "(orientation: portrait)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // display features
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if display is high DPI (retina)
isHighDPI :: Effect Boolean
isHighDPI = matchMedia "(-webkit-min-device-pixel-ratio: 2), (min-resolution: 192dpi)"

-- | Check if device supports touch
-- |
-- | Note: This is a heuristic based on media queries.
isTouch :: Effect Boolean
isTouch = matchMedia "(hover: none) and (pointer: coarse)"

-- | Check if currently printing
isPrint :: Effect Boolean
isPrint = matchMedia "print"
