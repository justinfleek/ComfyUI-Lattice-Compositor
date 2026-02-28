-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // mission
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand strategic layer: Mission, Promise, Overview.
-- |
-- | The foundational narrative. Every brand has an origin story, a reason
-- | for existing, and a way it wants to be perceived.
-- |
-- | From SMART Brand Ingestion Framework:
-- |   - Mission Statement: Canonical, locked copy — never paraphrase
-- |   - Brand Promise: Core commitment to user/customer
-- |   - Founding Context: Why the brand was created
-- |
-- | PURE DATA: All types are atoms and molecules for brand strategy.

module Hydrogen.Schema.Brand.Mission
  ( -- * Mission Statement
    MissionStatement
  , mkMissionStatement
  , unMissionStatement
  
  -- * Brand Promise
  , BrandPromise
  , mkBrandPromise
  , unBrandPromise
  
  -- * One-Line Description
  , OneLineDescription
  , mkOneLineDescription
  , unOneLineDescription
  
  -- * Founding Context
  , FoundingContext
  , mkFoundingContext
  , unFoundingContext
  
  -- * Industry Category
  , Industry
  , mkIndustry
  , unIndustry
  
  -- * Brand Overview (Compound)
  , BrandOverview
  , mkBrandOverview
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, trim, take) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mission statement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mission statement atom.
-- |
-- | A concise declaration of the brand's purpose and intended impact.
-- | This is LOCKED COPY — agents must never paraphrase, reword, or edit.
-- |
-- | Bounded: 1-2000 characters (enough for a full paragraph).
newtype MissionStatement = MissionStatement String

derive instance eqMissionStatement :: Eq MissionStatement
derive instance ordMissionStatement :: Ord MissionStatement

instance showMissionStatement :: Show MissionStatement where
  show (MissionStatement m) = "MissionStatement(" <> truncate 50 m <> ")"
    where
      truncate n s = 
        if String.length s <= n 
        then s 
        else String.take n s <> "..."

-- | Smart constructor with validation.
-- |
-- | Returns Nothing if empty or exceeds 2000 characters.
mkMissionStatement :: String -> Maybe MissionStatement
mkMissionStatement s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 2000
     then Just (MissionStatement trimmed)
     else Nothing

-- | Unwrap mission statement.
unMissionStatement :: MissionStatement -> String
unMissionStatement (MissionStatement m) = m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // brand promise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brand promise atom.
-- |
-- | The core commitment to the user/customer.
-- | Shorter than mission statement, typically 1-2 sentences.
-- |
-- | Bounded: 1-500 characters.
newtype BrandPromise = BrandPromise String

derive instance eqBrandPromise :: Eq BrandPromise
derive instance ordBrandPromise :: Ord BrandPromise

instance showBrandPromise :: Show BrandPromise where
  show (BrandPromise p) = "BrandPromise(" <> p <> ")"

-- | Smart constructor with validation.
mkBrandPromise :: String -> Maybe BrandPromise
mkBrandPromise s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just (BrandPromise trimmed)
     else Nothing

-- | Unwrap brand promise.
unBrandPromise :: BrandPromise -> String
unBrandPromise (BrandPromise p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // one-line description
-- ═════════════════════════════════════════════════════════════════════════════

-- | One-line description atom.
-- |
-- | What the brand does in a single sentence.
-- |
-- | Bounded: 1-200 characters.
newtype OneLineDescription = OneLineDescription String

derive instance eqOneLineDescription :: Eq OneLineDescription
derive instance ordOneLineDescription :: Ord OneLineDescription

instance showOneLineDescription :: Show OneLineDescription where
  show (OneLineDescription d) = "OneLineDescription(" <> d <> ")"

-- | Smart constructor with validation.
mkOneLineDescription :: String -> Maybe OneLineDescription
mkOneLineDescription s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 200
     then Just (OneLineDescription trimmed)
     else Nothing

-- | Unwrap one-line description.
unOneLineDescription :: OneLineDescription -> String
unOneLineDescription (OneLineDescription d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // founding context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Founding context atom.
-- |
-- | Why the brand was created and what problem it solves.
-- | Can be longer — the origin story narrative.
-- |
-- | Bounded: 1-5000 characters.
newtype FoundingContext = FoundingContext String

derive instance eqFoundingContext :: Eq FoundingContext
derive instance ordFoundingContext :: Ord FoundingContext

instance showFoundingContext :: Show FoundingContext where
  show (FoundingContext c) = "FoundingContext(" <> truncateCtx 50 c <> ")"
    where
      truncateCtx n s = 
        if String.length s <= n 
        then s 
        else String.take n s <> "..."

-- | Smart constructor with validation.
mkFoundingContext :: String -> Maybe FoundingContext
mkFoundingContext s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 5000
     then Just (FoundingContext trimmed)
     else Nothing

-- | Unwrap founding context.
unFoundingContext :: FoundingContext -> String
unFoundingContext (FoundingContext c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // industry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Industry/category atom.
-- |
-- | The brand's industry or category.
-- | Examples: "Technology", "Healthcare", "Financial Services"
-- |
-- | Bounded: 1-100 characters.
newtype Industry = Industry String

derive instance eqIndustry :: Eq Industry
derive instance ordIndustry :: Ord Industry

instance showIndustry :: Show Industry where
  show (Industry i) = "Industry(" <> i <> ")"

-- | Smart constructor with validation.
mkIndustry :: String -> Maybe Industry
mkIndustry s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 100
     then Just (Industry trimmed)
     else Nothing

-- | Unwrap industry.
unIndustry :: Industry -> String
unIndustry (Industry i) = i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // brand overview
-- ═════════════════════════════════════════════════════════════════════════════

-- | Brand overview compound.
-- |
-- | The foundational narrative combining all strategic elements.
-- | Some fields are optional (Maybe).
type BrandOverview =
  { description :: OneLineDescription
  , promise :: Maybe BrandPromise
  , mission :: Maybe MissionStatement
  , foundingContext :: Maybe FoundingContext
  , industry :: Maybe Industry
  , parentOrganization :: Maybe String  -- Optional parent company
  }

-- | Create a brand overview.
-- |
-- | Only description is required; other fields are optional.
mkBrandOverview :: OneLineDescription -> BrandOverview
mkBrandOverview description =
  { description
  , promise: Nothing
  , mission: Nothing
  , foundingContext: Nothing
  , industry: Nothing
  , parentOrganization: Nothing
  }
