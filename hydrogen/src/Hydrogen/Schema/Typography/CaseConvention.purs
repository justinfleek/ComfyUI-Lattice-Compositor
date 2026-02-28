-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // typography // case-convention
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CaseConvention - structural text casing conventions.
-- |
-- | Unlike TextTransform (which is visual-only rendering), CaseConvention
-- | represents **structural** transformations that modify the actual string
-- | content. These are used for:
-- |
-- | - Identifier generation (variable names, function names)
-- | - File naming conventions
-- | - API endpoint paths
-- | - Configuration keys
-- | - Database column names
-- | - CSS class names
-- | - URL slugs
-- |
-- | **Important distinction from TextTransform:**
-- | - TextTransform: Visual rendering, source preserved, CSS-based
-- | - CaseConvention: Structural change, modifies content, lossy
-- |
-- | CaseConvention transformations are generally **lossy** — converting
-- | "hello world" to "helloWorld" loses the space, and you cannot reliably
-- | recover the original without additional context.

module Hydrogen.Schema.Typography.CaseConvention
  ( CaseConvention
      ( CamelCase
      , PascalCase
      , SnakeCase
      , ScreamingSnakeCase
      , KebabCase
      , ScreamingKebabCase
      , DotCase
      , PathCase
      , FlatCase
      , ScreamingFlatCase
      , TitleCase
      , SentenceCase
      , TrainCase
      )
  , WordTransform(Lowercase, Uppercase, Capitalized)
  , UsageContext
      ( VariableName
      , FunctionName
      , ClassName
      , TypeName
      , ConstantName
      , EnumValue
      , FileName
      , DirectoryName
      , UrlSlug
      , UrlPath
      , CssClass
      , CssVariable
      , HtmlAttribute
      , JsonKey
      , YamlKey
      , XmlElement
      , DatabaseTable
      , DatabaseColumn
      , EnvironmentVariable
      , HttpHeader
      , CliFlag
      , PackageName
      , ModulePath
      , UiLabel
      , Headline
      , BodyText
      )
  , delimiter
  , wordTransform
  , firstWordTransform
  , isDelimited
  , preservesWordBoundaries
  , commonUsage
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // case convention
-- ═════════════════════════════════════════════════════════════════════════════

-- | Structural text casing conventions.
-- |
-- | Each convention defines:
-- | - How words are delimited (or concatenated)
-- | - How each word is transformed (case)
-- | - Whether the first word has special treatment
data CaseConvention
  = CamelCase
    -- ^ lowerCamelCase - first word lowercase, subsequent words capitalized
    -- ^ Used for: JavaScript variables, Java methods, JSON keys
    
  | PascalCase
    -- ^ UpperCamelCase - all words capitalized, concatenated
    -- ^ Used for: Class names, TypeScript types, React components
    
  | SnakeCase
    -- ^ lower_snake_case - words lowercase, delimited by underscore
    -- ^ Used for: Python variables, Ruby methods, PostgreSQL columns
    
  | ScreamingSnakeCase
    -- ^ SCREAMING_SNAKE_CASE - words uppercase, delimited by underscore
    -- ^ Used for: Constants, environment variables, enum values
    
  | KebabCase
    -- ^ kebab-case - words lowercase, delimited by hyphen
    -- ^ Used for: CSS classes, HTML attributes, URL slugs, CLI flags
    
  | ScreamingKebabCase
    -- ^ SCREAMING-KEBAB-CASE - words uppercase, delimited by hyphen
    -- ^ Used for: HTTP headers (X-Custom-Header), COBOL
    
  | DotCase
    -- ^ dot.case - words lowercase, delimited by period
    -- ^ Used for: Java package names, property paths, file extensions
    
  | PathCase
    -- ^ path/case - words lowercase, delimited by forward slash
    -- ^ Used for: File paths, URL paths, module paths
    
  | FlatCase
    -- ^ flatcase - all words lowercase, concatenated without delimiter
    -- ^ Used for: Package names, domain names (limited contexts)
    
  | ScreamingFlatCase
    -- ^ SCREAMINGFLATCASE - all words uppercase, concatenated
    -- ^ Used for: Legacy systems, specific identifiers
    
  | TitleCase
    -- ^ Title Case - each word capitalized, space delimited
    -- ^ Used for: Headlines, proper names, UI labels
    -- ^ Note: Locale-aware - articles/prepositions may stay lowercase
    
  | SentenceCase
    -- ^ Sentence case - first word capitalized, rest lowercase, space delimited
    -- ^ Used for: Body text, descriptions, natural language
    
  | TrainCase
    -- ^ Train-Case - each word capitalized, delimited by hyphen
    -- ^ Used for: HTTP headers, some identifier conventions

derive instance eqCaseConvention :: Eq CaseConvention
derive instance ordCaseConvention :: Ord CaseConvention

instance showCaseConvention :: Show CaseConvention where
  show CamelCase = "CamelCase"
  show PascalCase = "PascalCase"
  show SnakeCase = "SnakeCase"
  show ScreamingSnakeCase = "ScreamingSnakeCase"
  show KebabCase = "KebabCase"
  show ScreamingKebabCase = "ScreamingKebabCase"
  show DotCase = "DotCase"
  show PathCase = "PathCase"
  show FlatCase = "FlatCase"
  show ScreamingFlatCase = "ScreamingFlatCase"
  show TitleCase = "TitleCase"
  show SentenceCase = "SentenceCase"
  show TrainCase = "TrainCase"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | The delimiter character used between words, if any.
-- |
-- | Returns Nothing for conventions that concatenate without delimiter
-- | (CamelCase, PascalCase, FlatCase, ScreamingFlatCase).
delimiter :: CaseConvention -> Maybe Char
delimiter CamelCase = Nothing
delimiter PascalCase = Nothing
delimiter SnakeCase = Just '_'
delimiter ScreamingSnakeCase = Just '_'
delimiter KebabCase = Just '-'
delimiter ScreamingKebabCase = Just '-'
delimiter DotCase = Just '.'
delimiter PathCase = Just '/'
delimiter FlatCase = Nothing
delimiter ScreamingFlatCase = Nothing
delimiter TitleCase = Just ' '
delimiter SentenceCase = Just ' '
delimiter TrainCase = Just '-'

-- | How words (other than the first) are transformed.
-- |
-- | Returns a description of the transformation applied to each word.
-- | This is metadata for understanding the convention, not executable code.
data WordTransform
  = Lowercase      -- ^ word becomes "word"
  | Uppercase      -- ^ word becomes "WORD"
  | Capitalized    -- ^ word becomes "Word"

derive instance eqWordTransform :: Eq WordTransform

instance showWordTransform :: Show WordTransform where
  show Lowercase = "Lowercase"
  show Uppercase = "Uppercase"
  show Capitalized = "Capitalized"

-- | The transformation applied to words after the first.
wordTransform :: CaseConvention -> WordTransform
wordTransform CamelCase = Capitalized
wordTransform PascalCase = Capitalized
wordTransform SnakeCase = Lowercase
wordTransform ScreamingSnakeCase = Uppercase
wordTransform KebabCase = Lowercase
wordTransform ScreamingKebabCase = Uppercase
wordTransform DotCase = Lowercase
wordTransform PathCase = Lowercase
wordTransform FlatCase = Lowercase
wordTransform ScreamingFlatCase = Uppercase
wordTransform TitleCase = Capitalized
wordTransform SentenceCase = Lowercase
wordTransform TrainCase = Capitalized

-- | The transformation applied to the first word.
-- |
-- | Some conventions treat the first word differently (e.g., camelCase
-- | has lowercase first word, PascalCase has capitalized first word).
firstWordTransform :: CaseConvention -> WordTransform
firstWordTransform CamelCase = Lowercase
firstWordTransform PascalCase = Capitalized
firstWordTransform SnakeCase = Lowercase
firstWordTransform ScreamingSnakeCase = Uppercase
firstWordTransform KebabCase = Lowercase
firstWordTransform ScreamingKebabCase = Uppercase
firstWordTransform DotCase = Lowercase
firstWordTransform PathCase = Lowercase
firstWordTransform FlatCase = Lowercase
firstWordTransform ScreamingFlatCase = Uppercase
firstWordTransform TitleCase = Capitalized
firstWordTransform SentenceCase = Capitalized
firstWordTransform TrainCase = Capitalized

-- | Whether this convention uses a delimiter between words.
isDelimited :: CaseConvention -> Boolean
isDelimited conv = case delimiter conv of
  Just _ -> true
  Nothing -> false

-- | Whether word boundaries are preserved in the output.
-- |
-- | Delimited conventions preserve boundaries (you can split on delimiter).
-- | Concatenated conventions with capitalization preserve boundaries
-- | (you can detect capital letters). FlatCase loses boundaries entirely.
preservesWordBoundaries :: CaseConvention -> Boolean
preservesWordBoundaries FlatCase = false
preservesWordBoundaries ScreamingFlatCase = false
preservesWordBoundaries _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // common usage
-- ═════════════════════════════════════════════════════════════════════════════

-- | Common use cases for each convention.
-- |
-- | This is documentation encoded as data — agents can query this to select
-- | the appropriate convention for a given context.
data UsageContext
  = VariableName
  | FunctionName
  | ClassName
  | TypeName
  | ConstantName
  | EnumValue
  | FileName
  | DirectoryName
  | UrlSlug
  | UrlPath
  | CssClass
  | CssVariable
  | HtmlAttribute
  | JsonKey
  | YamlKey
  | XmlElement
  | DatabaseTable
  | DatabaseColumn
  | EnvironmentVariable
  | HttpHeader
  | CliFlag
  | PackageName
  | ModulePath
  | UiLabel
  | Headline
  | BodyText

derive instance eqUsageContext :: Eq UsageContext

instance showUsageContext :: Show UsageContext where
  show VariableName = "VariableName"
  show FunctionName = "FunctionName"
  show ClassName = "ClassName"
  show TypeName = "TypeName"
  show ConstantName = "ConstantName"
  show EnumValue = "EnumValue"
  show FileName = "FileName"
  show DirectoryName = "DirectoryName"
  show UrlSlug = "UrlSlug"
  show UrlPath = "UrlPath"
  show CssClass = "CssClass"
  show CssVariable = "CssVariable"
  show HtmlAttribute = "HtmlAttribute"
  show JsonKey = "JsonKey"
  show YamlKey = "YamlKey"
  show XmlElement = "XmlElement"
  show DatabaseTable = "DatabaseTable"
  show DatabaseColumn = "DatabaseColumn"
  show EnvironmentVariable = "EnvironmentVariable"
  show HttpHeader = "HttpHeader"
  show CliFlag = "CliFlag"
  show PackageName = "PackageName"
  show ModulePath = "ModulePath"
  show UiLabel = "UiLabel"
  show Headline = "Headline"
  show BodyText = "BodyText"

-- | Returns the common usage contexts for a case convention.
-- |
-- | Agents can use this to select conventions appropriate for their context,
-- | or to validate that a chosen convention is idiomatic for the use case.
commonUsage :: CaseConvention -> Array UsageContext
commonUsage CamelCase = 
  [ VariableName, FunctionName, JsonKey, YamlKey ]
commonUsage PascalCase = 
  [ ClassName, TypeName, FileName ]
commonUsage SnakeCase = 
  [ VariableName, FunctionName, DatabaseColumn, FileName, YamlKey ]
commonUsage ScreamingSnakeCase = 
  [ ConstantName, EnumValue, EnvironmentVariable ]
commonUsage KebabCase = 
  [ CssClass, CssVariable, HtmlAttribute, UrlSlug, CliFlag, FileName, DirectoryName ]
commonUsage ScreamingKebabCase = 
  [ HttpHeader ]
commonUsage DotCase = 
  [ PackageName, ModulePath ]
commonUsage PathCase = 
  [ UrlPath, ModulePath ]
commonUsage FlatCase = 
  [ PackageName ]
commonUsage ScreamingFlatCase = 
  []  -- Rare, legacy use only
commonUsage TitleCase = 
  [ Headline, UiLabel ]
commonUsage SentenceCase = 
  [ BodyText, UiLabel ]
commonUsage TrainCase = 
  [ HttpHeader ]
