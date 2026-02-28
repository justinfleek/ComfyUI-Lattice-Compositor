-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // brand // token // ref
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Token Reference System.
-- |
-- | This module provides infrastructure for referencing, grouping, and
-- | organizing design tokens. It enables:
-- |
-- | - **TokenRef**: Reference a token by name (aliasing)
-- | - **TokenGroup**: Organize related tokens (e.g., all primary colors)
-- | - **TokenSet**: Complete collection of all token groups
-- |
-- | ## Token Aliasing
-- |
-- | TokenRef allows semantic indirection:
-- | ```
-- | color.button.background -> color.primary.500
-- | color.link.default -> color.primary.600
-- | ```
-- |
-- | This enables theme switching - change the referenced value,
-- | all referencing tokens update automatically.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Token references enable coordination. When Agent A defines
-- | `color.primary.500`, Agent B can reference it without knowing
-- | the actual OKLCH value. The token system resolves references.

module Hydrogen.Schema.Brand.Token.Ref
  ( -- * Token Reference
    TokenRef
  , mkTokenRef
  , mkTokenRefAlias
  , tokenRefName
  , tokenRefTarget
  , tokenRefDisplay
  , isAlias
  , isDirectRef
  
  -- * Token Group
  , TokenGroup
  , mkTokenGroup
  , groupName
  , groupDesc
  , groupTokens
  , groupSize
  , groupDisplay
  , addToGroup
  , removeFromGroup
  , hasToken
  , lacksToken
  , isEmptyGroup
  
  -- * Token Set
  , TokenSet
  , emptyTokenSet
  , mkTokenSet
  , tokenSetName
  , tokenSetGroups
  , tokenSetDisplay
  , addGroup
  , removeGroup
  , getGroup
  , hasGroup
  , allTokenNames
  , tokenSetSize
  , isEmptySet
  
  -- * Any Token (Union Type)
  , AnyToken(..)
  , anyTokenName
  , anyTokenCategory
  , anyTokenDisplay
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , (==)
  , (/=)
  , (+)
  , (>=)
  , (<)
  , (<>)
  , map
  , not
  , otherwise
  )

import Data.Array (filter, foldl, length, snoc)
import Data.Array (concatMap) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(..)
  , unTokenName
  )

import Hydrogen.Schema.Brand.Token.Color (ColorToken, colorTokenName)
import Hydrogen.Schema.Brand.Token.Spacing (SpacingToken, spacingTokenName)
import Hydrogen.Schema.Brand.Token.Size (SizeToken, sizeTokenName)
import Hydrogen.Schema.Brand.Token.Radius (RadiusToken, radiusTokenName)
import Hydrogen.Schema.Brand.Token.Shadow (ShadowToken, shadowTokenName)
import Hydrogen.Schema.Brand.Token.Type (TypeToken, typeTokenName)
import Hydrogen.Schema.Brand.Token.Duration (DurationToken, durationTokenName)
import Hydrogen.Schema.Brand.Token.Easing (EasingToken, easingTokenName)
import Hydrogen.Schema.Brand.Token.ZIndex (ZIndexToken, zIndexTokenName)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // token // ref
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a token (possibly an alias).
-- |
-- | A token reference can be:
-- | 1. A direct reference (name only)
-- | 2. An alias (name points to another token's name)
type TokenRef =
  { name :: TokenName      -- ^ This token's name
  , target :: Maybe TokenName  -- ^ Target token (if alias)
  }

-- | Create a direct token reference.
mkTokenRef :: TokenName -> TokenRef
mkTokenRef name =
  { name: name
  , target: Nothing
  }

-- | Create an alias token reference.
mkTokenRefAlias :: TokenName -> TokenName -> TokenRef
mkTokenRefAlias name target =
  { name: name
  , target: Just target
  }

-- | Get the reference name.
tokenRefName :: TokenRef -> TokenName
tokenRefName r = r.name

-- | Get the target (if alias).
tokenRefTarget :: TokenRef -> Maybe TokenName
tokenRefTarget r = r.target

-- | Check if this is an alias.
isAlias :: TokenRef -> Boolean
isAlias r = case r.target of
  Just _ -> true
  Nothing -> false

-- | Check if this is a direct reference (not an alias).
isDirectRef :: TokenRef -> Boolean
isDirectRef r = not (isAlias r)

-- | Display a token reference as a string.
-- |
-- | Direct: "color.primary.500"
-- | Alias: "color.button.bg -> color.primary.500"
tokenRefDisplay :: TokenRef -> String
tokenRefDisplay r = case r.target of
  Nothing -> unTokenName r.name
  Just target -> unTokenName r.name <> " -> " <> unTokenName target

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // token // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group of related tokens.
-- |
-- | Examples:
-- | - "color.primary" group with 50/100/200/.../900/950 shades
-- | - "spacing" group with xs/sm/md/lg/xl/2xl values
-- | - "type.heading" group with h1/h2/h3/h4/h5/h6 styles
type TokenGroup =
  { name :: String            -- ^ Group name (e.g., "color.primary")
  , description :: TokenDesc  -- ^ Group description
  , tokens :: Array TokenName -- ^ Token names in this group
  }

-- | Create a token group.
mkTokenGroup :: String -> TokenDesc -> Array TokenName -> TokenGroup
mkTokenGroup name desc tokens =
  { name: name
  , description: desc
  , tokens: tokens
  }

-- | Get group name.
groupName :: TokenGroup -> String
groupName g = g.name

-- | Get group description.
groupDesc :: TokenGroup -> TokenDesc
groupDesc g = g.description

-- | Get tokens in group.
groupTokens :: TokenGroup -> Array TokenName
groupTokens g = g.tokens

-- | Get number of tokens in group.
groupSize :: TokenGroup -> Int
groupSize g = length g.tokens

-- | Add a token to a group.
addToGroup :: TokenName -> TokenGroup -> TokenGroup
addToGroup tokenName g =
  g { tokens = snoc g.tokens tokenName }

-- | Remove a token from a group.
removeFromGroup :: TokenName -> TokenGroup -> TokenGroup
removeFromGroup tokenName g =
  g { tokens = filter (\t -> unTokenName t /= unTokenName tokenName) g.tokens }

-- | Check if group contains a token.
hasToken :: TokenName -> TokenGroup -> Boolean
hasToken tokenName g =
  length (filter (\t -> unTokenName t == unTokenName tokenName) g.tokens) >= 1

-- | Check if group does NOT contain a token.
lacksToken :: TokenName -> TokenGroup -> Boolean
lacksToken tokenName g = not (hasToken tokenName g)

-- | Check if group is empty.
isEmptyGroup :: TokenGroup -> Boolean
isEmptyGroup g = length g.tokens == 0

-- | Display a token group as a string.
-- |
-- | Example: "color.primary (11 tokens)"
groupDisplay :: TokenGroup -> String
groupDisplay g = g.name <> " (" <> show (groupSize g) <> " tokens)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // token // set
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete set of token groups.
-- |
-- | A TokenSet is the top-level container for all design tokens.
-- | It organizes tokens into groups by category or semantic meaning.
type TokenSet =
  { name :: String              -- ^ Set name (e.g., "default", "dark")
  , groups :: Array TokenGroup  -- ^ All token groups
  }

-- | Create an empty token set.
emptyTokenSet :: String -> TokenSet
emptyTokenSet name =
  { name: name
  , groups: []
  }

-- | Create a token set with groups.
mkTokenSet :: String -> Array TokenGroup -> TokenSet
mkTokenSet name groups =
  { name: name
  , groups: groups
  }

-- | Get set name.
tokenSetName :: TokenSet -> String
tokenSetName s = s.name

-- | Get all groups.
tokenSetGroups :: TokenSet -> Array TokenGroup
tokenSetGroups s = s.groups

-- | Add a group to the set.
addGroup :: TokenGroup -> TokenSet -> TokenSet
addGroup group set =
  set { groups = snoc set.groups group }

-- | Get a group by name.
getGroup :: String -> TokenSet -> Maybe TokenGroup
getGroup name set =
  case filter (\g -> g.name == name) set.groups of
    [] -> Nothing
    [g] -> Just g
    _ -> Nothing  -- Multiple matches (shouldn't happen)

-- | Get all token names in the set.
allTokenNames :: TokenSet -> Array TokenName
allTokenNames set = Array.concatMap groupTokens set.groups

-- | Get total number of tokens in the set.
tokenSetSize :: TokenSet -> Int
tokenSetSize set = foldl (+) 0 (map groupSize set.groups)

-- | Check if a set contains a group by name.
hasGroup :: String -> TokenSet -> Boolean
hasGroup name set = case getGroup name set of
  Just _ -> true
  Nothing -> false

-- | Remove a group from the set by name.
removeGroup :: String -> TokenSet -> TokenSet
removeGroup name set =
  set { groups = filter (\g -> g.name /= name) set.groups }

-- | Check if set is empty.
isEmptySet :: TokenSet -> Boolean
isEmptySet set = length set.groups == 0

-- | Display a token set as a string.
-- |
-- | Example: "default (5 groups, 47 tokens)"
tokenSetDisplay :: TokenSet -> String
tokenSetDisplay set = 
  set.name <> " (" <> 
  show (length set.groups) <> " groups, " <> 
  show (tokenSetSize set) <> " tokens)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // any // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Union type for any token.
-- |
-- | Useful for heterogeneous collections and serialization.
data AnyToken
  = ColorTok ColorToken
  | SpacingTok SpacingToken
  | SizeTok SizeToken
  | RadiusTok RadiusToken
  | ShadowTok ShadowToken
  | TypeTok TypeToken
  | DurationTok DurationToken
  | EasingTok EasingToken
  | ZIndexTok ZIndexToken

instance showAnyToken :: Show AnyToken where
  show (ColorTok _) = "ColorToken"
  show (SpacingTok _) = "SpacingToken"
  show (SizeTok _) = "SizeToken"
  show (RadiusTok _) = "RadiusToken"
  show (ShadowTok _) = "ShadowToken"
  show (TypeTok _) = "TypeToken"
  show (DurationTok _) = "DurationToken"
  show (EasingTok _) = "EasingToken"
  show (ZIndexTok _) = "ZIndexToken"

-- | Eq instance for AnyToken - compares by name.
-- |
-- | Two tokens are equal if they have the same name, regardless of type.
-- | This enables lookup operations in heterogeneous collections.
instance eqAnyToken :: Eq AnyToken where
  eq a b = unTokenName (anyTokenName a) == unTokenName (anyTokenName b)

-- | Ord instance for AnyToken - orders by name.
-- |
-- | Enables sorting and ordered collections of mixed token types.
instance ordAnyToken :: Ord AnyToken where
  compare a b = compareStrings (unTokenName (anyTokenName a)) (unTokenName (anyTokenName b))
    where
    compareStrings :: String -> String -> Ordering
    compareStrings s1 s2
      | s1 == s2 = EQ
      | s1 < s2 = LT
      | otherwise = GT

-- | Get the name of any token.
anyTokenName :: AnyToken -> TokenName
anyTokenName = case _ of
  ColorTok t -> colorTokenName t
  SpacingTok t -> spacingTokenName t
  SizeTok t -> sizeTokenName t
  RadiusTok t -> radiusTokenName t
  ShadowTok t -> shadowTokenName t
  TypeTok t -> typeTokenName t
  DurationTok t -> durationTokenName t
  EasingTok t -> easingTokenName t
  ZIndexTok t -> zIndexTokenName t

-- | Get the category of any token.
anyTokenCategory :: AnyToken -> TokenCategory
anyTokenCategory = case _ of
  ColorTok _ -> CategoryColor
  SpacingTok _ -> CategorySpacing
  SizeTok _ -> CategorySize
  RadiusTok _ -> CategoryRadius
  ShadowTok _ -> CategoryShadow
  TypeTok _ -> CategoryType
  DurationTok _ -> CategoryDuration
  EasingTok _ -> CategoryEasing
  ZIndexTok _ -> CategoryZIndex

-- | Display any token as a string with type and name.
-- |
-- | Example: "ColorToken(color.primary.500)"
anyTokenDisplay :: AnyToken -> String
anyTokenDisplay t = show t <> "(" <> unTokenName (anyTokenName t) <> ")"
