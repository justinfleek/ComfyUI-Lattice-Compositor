-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ARIA Landmark Roles — Page region navigation
-- |
-- | Landmarks provide a way to navigate to major sections of a page.
-- | Screen reader users can jump between landmarks using keyboard shortcuts.
-- |
-- | ## Best Practices
-- | - Use exactly one main landmark per page
-- | - banner and contentinfo should be at the top level
-- | - Multiple navigation landmarks should have aria-label
-- | - search is for site-wide search, not page filtering
-- |
-- | ## HTML5 Mapping
-- | Many HTML5 elements automatically provide landmarks:
-- | - <header> (top-level) → banner
-- | - <nav> → navigation
-- | - <main> → main
-- | - <aside> → complementary
-- | - <footer> (top-level) → contentinfo
-- | - <form> with accessible name → form
-- | - <section> with accessible name → region
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/#landmark_roles
module Hydrogen.Schema.Accessibility.Landmark
  ( -- * Landmark Role
    LandmarkRole(..)
  , landmarkToString
  , landmarkFromString
    -- * Landmark Queries
  , isUniqueLandmark
  , requiresLabel
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // landmark role
-- ═════════════════════════════════════════════════════════════════════════════

-- | Landmark roles for page regions.
data LandmarkRole
  = LandmarkBanner        -- ^ Site header (logo, site name)
  | LandmarkComplementary -- ^ Supporting content (sidebars)
  | LandmarkContentinfo   -- ^ Site footer (copyright, links)
  | LandmarkForm          -- ^ Form landmark (needs accessible name)
  | LandmarkMain          -- ^ Primary content (exactly one per page)
  | LandmarkNavigation    -- ^ Navigation links
  | LandmarkRegion        -- ^ Generic region (needs accessible name)
  | LandmarkSearch        -- ^ Search functionality

derive instance eqLandmarkRole :: Eq LandmarkRole

instance showLandmarkRole :: Show LandmarkRole where
  show = landmarkToString

-- | Convert landmark role to ARIA role string.
landmarkToString :: LandmarkRole -> String
landmarkToString LandmarkBanner = "banner"
landmarkToString LandmarkComplementary = "complementary"
landmarkToString LandmarkContentinfo = "contentinfo"
landmarkToString LandmarkForm = "form"
landmarkToString LandmarkMain = "main"
landmarkToString LandmarkNavigation = "navigation"
landmarkToString LandmarkRegion = "region"
landmarkToString LandmarkSearch = "search"

-- | Parse landmark from string.
landmarkFromString :: String -> Maybe LandmarkRole
landmarkFromString "banner" = Just LandmarkBanner
landmarkFromString "complementary" = Just LandmarkComplementary
landmarkFromString "contentinfo" = Just LandmarkContentinfo
landmarkFromString "form" = Just LandmarkForm
landmarkFromString "main" = Just LandmarkMain
landmarkFromString "navigation" = Just LandmarkNavigation
landmarkFromString "region" = Just LandmarkRegion
landmarkFromString "search" = Just LandmarkSearch
landmarkFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // landmark queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Whether this landmark should appear exactly once per page.
-- |
-- | - main: Exactly one required
-- | - banner: At most one at top level
-- | - contentinfo: At most one at top level
isUniqueLandmark :: LandmarkRole -> Boolean
isUniqueLandmark LandmarkMain = true
isUniqueLandmark LandmarkBanner = true
isUniqueLandmark LandmarkContentinfo = true
isUniqueLandmark _ = false

-- | Whether this landmark requires an accessible name to be useful.
-- |
-- | - form: Must have aria-label/aria-labelledby
-- | - region: Must have aria-label/aria-labelledby
-- | - navigation: Recommended when multiple exist
requiresLabel :: LandmarkRole -> Boolean
requiresLabel LandmarkForm = true
requiresLabel LandmarkRegion = true
requiresLabel _ = false
