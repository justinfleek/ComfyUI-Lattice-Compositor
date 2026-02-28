-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                     // hydrogen // convention
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Straylight typographical conventions
-- |
-- | This module encodes the precise formatting rules for straylight code.
-- | All lines are exactly 80 characters. Titles are right-aligned to column 80.
-- |
-- | ## Line Types
-- |
-- | - **Heavy (`━`)**: File-level framing, module boundaries
-- | - **Double (`═`)**: Major sections within a file  
-- | - **Light (`─`)**: Subsections, nested structure
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Convention as C
-- |
-- | -- Generate headers
-- | C.heavyHeader "// hydrogen // color"
-- | -- "-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
-- | -- "--                                                          // hydrogen // color"
-- | -- "-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
-- |
-- | -- Validate a title line
-- | C.validateTitle "--                                                          // hydrogen // color"
-- | -- Right unit (valid)
-- |
-- | C.validateTitle "--                                                         // hydrogen // color"
-- | -- Left "Line is 79 characters, expected 80"
-- | ```
module Hydrogen.Convention
  ( -- * Constants
    lineWidth
  , commentPrefix
  , commentPrefixLen
  , titlePrefix
  , titlePrefixLen
    -- * Line Characters
  , LineType(..)
  , lineChar
  , lineCharCount
    -- * Generation
  , line
  , title
  , header
  , heavyHeader
  , doubleHeader
  , lightHeader
    -- * Validation
  , validateLine
  , validateTitle
  , validateHeader
    -- * Parsing
  , parseTitle
  , extractTitleText
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Nothing, Just))
import Data.String as String
import Data.String.CodeUnits as CU

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Canonical line width for all straylight code
-- |
-- | All lines are exactly 80 characters. No exceptions.
lineWidth :: Int
lineWidth = 80

-- | Comment prefix for PureScript/Haskell: "-- "
commentPrefix :: String
commentPrefix = "-- "

-- | Length of comment prefix: 3
commentPrefixLen :: Int
commentPrefixLen = 3

-- | Title line prefix: "--" (no trailing space)
titlePrefix :: String
titlePrefix = "--"

-- | Length of title prefix: 2
titlePrefixLen :: Int
titlePrefixLen = 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // line // characters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line types with their Unicode box-drawing characters
data LineType
  = Heavy   -- ^ ━ File-level framing
  | Double  -- ^ ═ Major sections
  | Light   -- ^ ─ Subsections

derive instance eqLineType :: Eq LineType

-- | Get the Unicode character for a line type
lineChar :: LineType -> String
lineChar = case _ of
  Heavy  -> "━"
  Double -> "═"
  Light  -> "─"

-- | Number of line characters needed to reach 80 columns
-- |
-- | For "-- " prefix (3 chars), we need 77 line chars.
lineCharCount :: Int
lineCharCount = lineWidth - commentPrefixLen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a line of the specified type
-- |
-- | ```purescript
-- | line Heavy
-- | -- "-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
-- | ```
line :: LineType -> String
line lt = commentPrefix <> repeatStr lineCharCount (lineChar lt)

-- | Generate a title line, right-aligned to column 80
-- |
-- | ```purescript
-- | title "// hydrogen // color"
-- | -- "--                                                          // hydrogen // color"
-- | ```
-- |
-- | Returns `Nothing` if the title is too long (> 78 characters).
title :: String -> Maybe String
title t =
  let
    titleLen = CU.length t
    spacesNeeded = lineWidth - titlePrefixLen - titleLen
  in
    if spacesNeeded < 0
      then Nothing
      else Just $ titlePrefix <> repeatStr spacesNeeded " " <> t

-- | Generate a complete header block (line, title, line)
-- |
-- | Returns `Nothing` if the title is too long.
header :: LineType -> String -> Maybe String
header lt t = do
  titleLine <- title t
  let l = line lt
  pure $ l <> "\n" <> titleLine <> "\n" <> l

-- | Generate a heavy (file-level) header
heavyHeader :: String -> Maybe String
heavyHeader = header Heavy

-- | Generate a double (major section) header
doubleHeader :: String -> Maybe String
doubleHeader = header Double

-- | Generate a light (subsection) header
lightHeader :: String -> Maybe String
lightHeader = header Light

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate that a line is exactly 80 characters and uses correct line chars
validateLine :: String -> Either String Unit
validateLine s =
  let len = CU.length s
  in
    if len /= lineWidth
      then Left $ "Line is " <> show len <> " characters, expected " <> show lineWidth
      else if not (String.take commentPrefixLen s == commentPrefix)
        then Left $ "Line must start with \"" <> commentPrefix <> "\""
        else Right unit

-- | Validate that a title line is exactly 80 characters with correct format
validateTitle :: String -> Either String Unit
validateTitle s =
  let len = CU.length s
  in
    if len /= lineWidth
      then Left $ "Title is " <> show len <> " characters, expected " <> show lineWidth
      else if not (String.take titlePrefixLen s == titlePrefix)
        then Left $ "Title must start with \"" <> titlePrefix <> "\""
        else Right unit

-- | Validate a complete header block (3 lines)
validateHeader :: String -> Either String Unit
validateHeader s =
  case String.split (String.Pattern "\n") s of
    [l1, t, l2] -> do
      validateLine l1
      validateTitle t
      validateLine l2
      if l1 /= l2
        then Left "Opening and closing lines must match"
        else Right unit
    _ -> Left "Header must be exactly 3 lines"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse a title line and extract its components
-- |
-- | Returns `{ prefix, spaces, title }` or `Nothing` if invalid.
parseTitle :: String -> Maybe { prefix :: String, spaces :: Int, title :: String }
parseTitle s =
  let len = CU.length s
  in
    if len /= lineWidth
      then Nothing
      else if not (String.take titlePrefixLen s == titlePrefix)
        then Nothing
        else
          let
            afterPrefix = String.drop titlePrefixLen s
            trimmed = String.trim afterPrefix
            spaces = CU.length afterPrefix - CU.length trimmed
          in
            Just { prefix: titlePrefix, spaces, title: trimmed }

-- | Extract just the title text from a title line
-- |
-- | ```purescript
-- | extractTitleText "--                                                          // hydrogen // color"
-- | -- Just "// hydrogen // color"
-- | ```
extractTitleText :: String -> Maybe String
extractTitleText s = _.title <$> parseTitle s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Repeat a string n times
repeatStr :: Int -> String -> String
repeatStr n s
  | n <= 0 = ""
  | otherwise = s <> repeatStr (n - 1) s
