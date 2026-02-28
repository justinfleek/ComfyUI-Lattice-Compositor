-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // typography // type-role
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TypeRole — semantic purpose of text in a design system.
-- |
-- | ## Design Philosophy
-- |
-- | TypeRole goes beyond hierarchy levels (H1-H6) to describe the
-- | semantic PURPOSE of text. This enables:
-- |
-- | - Consistent styling by meaning, not just size
-- | - Accessibility (screen readers, semantic HTML)
-- | - Design system token mapping
-- | - Intent-driven typography
-- |
-- | ## Role Categories
-- |
-- | **Display**: Large, attention-grabbing text
-- | - Hero, Display, Title, Subtitle
-- |
-- | **Content**: Reading and body text
-- | - Body, BodyLarge, BodySmall, Lead
-- |
-- | **UI**: Interface text
-- | - Label, Button, Input, Link, Navigation
-- |
-- | **Supporting**: Metadata and supplementary
-- | - Caption, Helper, Error, Success, Warning
-- |
-- | **Code**: Technical text
-- | - Code, CodeBlock, PreFormatted
-- |
-- | ## Dependencies
-- |
-- | None — this is a pure enumeration type.
-- |
-- | ## Dependents
-- |
-- | - TypeStyle (role-based styling)
-- | - Theme (semantic token mapping)
-- | - Accessibility (ARIA roles)

module Hydrogen.Schema.Typography.TypeRole
  ( -- * TypeRole Type
    TypeRole(..)
  
  -- * Category Classification
  , RoleCategory(..)
  , category
  
  -- * Properties
  , isDisplay
  , isContent
  , isUI
  , isSupporting
  , isCode
  , isHeading
  
  -- * Hierarchy Mapping
  , toHeadingLevel
  , defaultImportance
  
  -- * Display
  , roleName
  , roleDescription
  , roleInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // type role enum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic role of text.
-- |
-- | Describes the PURPOSE of text, enabling consistent styling
-- | and proper accessibility semantics.
data TypeRole
  -- Display roles (large, attention-grabbing)
  = Hero           -- ^ Largest display text (marketing, landing pages)
  | Display        -- ^ Large display text (section headers)
  | Title          -- ^ Primary title (page/section)
  | Subtitle       -- ^ Secondary title (accompanies Title)
  
  -- Content roles (reading text)
  | Lead           -- ^ Introductory paragraph (larger body)
  | Body           -- ^ Primary reading text
  | BodyLarge      -- ^ Larger body text (emphasis)
  | BodySmall      -- ^ Smaller body text (secondary)
  
  -- UI roles (interface text)
  | Label          -- ^ Form labels
  | Button         -- ^ Button text
  | Input          -- ^ Input field text
  | Link           -- ^ Hyperlink text
  | Navigation     -- ^ Nav menu text
  | Tab            -- ^ Tab labels
  | Chip           -- ^ Tag/chip text
  | Badge          -- ^ Badge/indicator text
  
  -- Supporting roles (metadata, feedback)
  | Caption        -- ^ Image captions, metadata
  | Helper         -- ^ Help text, hints
  | Placeholder    -- ^ Placeholder text
  | Error          -- ^ Error messages
  | Success        -- ^ Success messages
  | Warning        -- ^ Warning messages
  | Info           -- ^ Informational messages
  | Overline       -- ^ Category/eyebrow text
  | Footnote       -- ^ Footnotes, citations
  
  -- Code roles (technical text)
  | Code           -- ^ Inline code
  | CodeBlock      -- ^ Block of code
  | PreFormatted   -- ^ Preformatted text
  | Keyboard       -- ^ Keyboard shortcuts
  | Variable       -- ^ Code variables
  | Output         -- ^ Terminal/console output

derive instance eqTypeRole :: Eq TypeRole
derive instance ordTypeRole :: Ord TypeRole

instance showTypeRole :: Show TypeRole where
  show Hero = "Hero"
  show Display = "Display"
  show Title = "Title"
  show Subtitle = "Subtitle"
  show Lead = "Lead"
  show Body = "Body"
  show BodyLarge = "BodyLarge"
  show BodySmall = "BodySmall"
  show Label = "Label"
  show Button = "Button"
  show Input = "Input"
  show Link = "Link"
  show Navigation = "Navigation"
  show Tab = "Tab"
  show Chip = "Chip"
  show Badge = "Badge"
  show Caption = "Caption"
  show Helper = "Helper"
  show Placeholder = "Placeholder"
  show Error = "Error"
  show Success = "Success"
  show Warning = "Warning"
  show Info = "Info"
  show Overline = "Overline"
  show Footnote = "Footnote"
  show Code = "Code"
  show CodeBlock = "CodeBlock"
  show PreFormatted = "PreFormatted"
  show Keyboard = "Keyboard"
  show Variable = "Variable"
  show Output = "Output"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // role categories
-- ═════════════════════════════════════════════════════════════════════════════

-- | Category grouping for type roles.
data RoleCategory
  = DisplayCategory     -- ^ Display/heading roles
  | ContentCategory     -- ^ Body/reading text
  | UICategory          -- ^ Interface elements
  | SupportingCategory  -- ^ Metadata, feedback
  | CodeCategory        -- ^ Technical/code text

derive instance eqRoleCategory :: Eq RoleCategory
derive instance ordRoleCategory :: Ord RoleCategory

instance showRoleCategory :: Show RoleCategory where
  show DisplayCategory = "Display"
  show ContentCategory = "Content"
  show UICategory = "UI"
  show SupportingCategory = "Supporting"
  show CodeCategory = "Code"

-- | Get the category for a role.
category :: TypeRole -> RoleCategory
category Hero = DisplayCategory
category Display = DisplayCategory
category Title = DisplayCategory
category Subtitle = DisplayCategory
category Lead = ContentCategory
category Body = ContentCategory
category BodyLarge = ContentCategory
category BodySmall = ContentCategory
category Label = UICategory
category Button = UICategory
category Input = UICategory
category Link = UICategory
category Navigation = UICategory
category Tab = UICategory
category Chip = UICategory
category Badge = UICategory
category Caption = SupportingCategory
category Helper = SupportingCategory
category Placeholder = SupportingCategory
category Error = SupportingCategory
category Success = SupportingCategory
category Warning = SupportingCategory
category Info = SupportingCategory
category Overline = SupportingCategory
category Footnote = SupportingCategory
category Code = CodeCategory
category CodeBlock = CodeCategory
category PreFormatted = CodeCategory
category Keyboard = CodeCategory
category Variable = CodeCategory
category Output = CodeCategory

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if role is in Display category.
isDisplay :: TypeRole -> Boolean
isDisplay role = category role == DisplayCategory

-- | Check if role is in Content category.
isContent :: TypeRole -> Boolean
isContent role = category role == ContentCategory

-- | Check if role is in UI category.
isUI :: TypeRole -> Boolean
isUI role = category role == UICategory

-- | Check if role is in Supporting category.
isSupporting :: TypeRole -> Boolean
isSupporting role = category role == SupportingCategory

-- | Check if role is in Code category.
isCode :: TypeRole -> Boolean
isCode role = category role == CodeCategory

-- | Check if role represents a heading (for accessibility).
isHeading :: TypeRole -> Boolean
isHeading Hero = true
isHeading Display = true
isHeading Title = true
isHeading Subtitle = true
isHeading _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // hierarchy mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map role to HTML heading level (1-6).
-- |
-- | Returns Nothing for non-heading roles.
toHeadingLevel :: TypeRole -> Maybe Int
toHeadingLevel Hero = Just 1
toHeadingLevel Display = Just 1
toHeadingLevel Title = Just 2
toHeadingLevel Subtitle = Just 3
toHeadingLevel _ = Nothing

-- | Default importance weight (0-100).
-- |
-- | Higher = more important in visual hierarchy.
defaultImportance :: TypeRole -> Int
defaultImportance Hero = 100
defaultImportance Display = 95
defaultImportance Title = 90
defaultImportance Subtitle = 85
defaultImportance Lead = 75
defaultImportance Body = 70
defaultImportance BodyLarge = 72
defaultImportance BodySmall = 68
defaultImportance Label = 60
defaultImportance Button = 65
defaultImportance Input = 55
defaultImportance Link = 60
defaultImportance Navigation = 65
defaultImportance Tab = 60
defaultImportance Chip = 50
defaultImportance Badge = 55
defaultImportance Caption = 45
defaultImportance Helper = 40
defaultImportance Placeholder = 35
defaultImportance Error = 75  -- Errors need visibility
defaultImportance Success = 70
defaultImportance Warning = 75
defaultImportance Info = 65
defaultImportance Overline = 50
defaultImportance Footnote = 35
defaultImportance Code = 60
defaultImportance CodeBlock = 60
defaultImportance PreFormatted = 55
defaultImportance Keyboard = 55
defaultImportance Variable = 55
defaultImportance Output = 50

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a human-readable name for the role.
roleName :: TypeRole -> String
roleName = show

-- | Get full role information (name and description).
roleInfo :: TypeRole -> String
roleInfo role = roleName role <> ": " <> roleDescription role

-- | Get a description of the role's purpose.
roleDescription :: TypeRole -> String
roleDescription Hero = "Largest display text for maximum impact"
roleDescription Display = "Large display text for section headers"
roleDescription Title = "Primary title for pages or sections"
roleDescription Subtitle = "Secondary title accompanying a Title"
roleDescription Lead = "Introductory paragraph with emphasis"
roleDescription Body = "Primary reading text for content"
roleDescription BodyLarge = "Larger body text for emphasis"
roleDescription BodySmall = "Smaller body text for secondary content"
roleDescription Label = "Form field labels"
roleDescription Button = "Button and action text"
roleDescription Input = "Text input field content"
roleDescription Link = "Hyperlink and navigation text"
roleDescription Navigation = "Navigation menu items"
roleDescription Tab = "Tab labels in tab interfaces"
roleDescription Chip = "Tag and chip text"
roleDescription Badge = "Badge and indicator text"
roleDescription Caption = "Image captions and metadata"
roleDescription Helper = "Help text and hints"
roleDescription Placeholder = "Placeholder text in inputs"
roleDescription Error = "Error and validation messages"
roleDescription Success = "Success confirmation messages"
roleDescription Warning = "Warning and caution messages"
roleDescription Info = "Informational messages"
roleDescription Overline = "Category labels and eyebrow text"
roleDescription Footnote = "Footnotes and citations"
roleDescription Code = "Inline code snippets"
roleDescription CodeBlock = "Multi-line code blocks"
roleDescription PreFormatted = "Preformatted text preserving whitespace"
roleDescription Keyboard = "Keyboard shortcut representations"
roleDescription Variable = "Variable names in code"
roleDescription Output = "Terminal and console output"
