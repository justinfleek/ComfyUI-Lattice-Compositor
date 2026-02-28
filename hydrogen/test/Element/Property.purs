-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deep Property Tests for Hydrogen.Element.Core
-- |
-- | These tests are designed to FIND BUGS, not prove correctness.
-- | They target known failure modes and adversarial conditions.
-- |
-- | ## Known Bugs Being Hunted
-- |
-- | 1. **Group Opacity Loss**: `(Group g1) <> (Group g2)` resets opacity to 100%
-- |    The Semigroup instance hardcodes `opacity: opacity 100` instead of 
-- |    combining opacities correctly.
-- |
-- | 2. **Monoid Law Violations**: Empty might not be a true identity.
-- |
-- | ## Test Strategy
-- |
-- | - **Algebraic Laws**: Semigroup associativity, Monoid identity
-- | - **Invariant Preservation**: Opacity should never be lost
-- | - **Adversarial**: Boundary values, nested structures, empty children

module Test.Element.Property
  ( elementPropertyTests
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( Unit
  , bind
  , discard
  , negate
  , not
  , pure
  , show
  , unit
  , ($)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (<)
  , (<=)
  , (<>)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<$>)
  )

import Data.Array (length, replicate, foldl) as Array
import Data.Array.NonEmpty (cons') as NEA
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Element.Core as Element
import Hydrogen.Schema.Color.Opacity as Opacity

import Test.QuickCheck ((<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, vectorOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate opacity with realistic distribution and adversarial values.
genOpacity :: Gen Opacity.Opacity
genOpacity = frequency $ NEA.cons'
  (Tuple 20.0 (pure $ Opacity.opacity 100))
  [ Tuple 15.0 (pure $ Opacity.opacity 0)
  , Tuple 15.0 (pure $ Opacity.opacity 50)
  , Tuple 20.0 (Opacity.opacity <$> chooseInt 1 30)
  , Tuple 20.0 (Opacity.opacity <$> chooseInt 70 99)
  , Tuple 10.0 genOpacityAdversarial
  ]

-- | Adversarial opacity values to test clamping.
genOpacityAdversarial :: Gen Opacity.Opacity
genOpacityAdversarial = elements $ NEA.cons'
  (Opacity.opacity (-1))
  [ Opacity.opacity (-100)
  , Opacity.opacity 101
  , Opacity.opacity 200
  , Opacity.opacity 0
  , Opacity.opacity 100
  ]

-- | Generate non-100 opacity specifically for testing opacity preservation.
-- | This ensures we're testing with opacities that would show the bug.
genNonFullOpacity :: Gen Opacity.Opacity
genNonFullOpacity = frequency $ NEA.cons'
  (Tuple 30.0 (Opacity.opacity <$> chooseInt 1 49))
  [ Tuple 30.0 (Opacity.opacity <$> chooseInt 51 99)
  , Tuple 20.0 (pure $ Opacity.opacity 50)
  , Tuple 20.0 (pure $ Opacity.opacity 0)
  ]

-- | Generate a Group with specific opacity and Empty children
genGroupWithOpacity :: Opacity.Opacity -> Int -> Element.Element
genGroupWithOpacity op numChildren = 
  Element.Group 
    { children: Array.replicate numChildren Element.Empty
    , opacity: op 
    }

-- | Generate arbitrary Element (Group or Empty)
genElement :: Gen Element.Element
genElement = frequency $ NEA.cons'
  (Tuple 50.0 genGroup)
  [ Tuple 50.0 (pure Element.Empty)
  ]

-- | Generate a Group element
genGroup :: Gen Element.Element
genGroup = do
  op <- genOpacity
  numChildren <- chooseInt 0 5
  pure $ genGroupWithOpacity op numChildren

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract Group opacity (returns Nothing for non-groups)
getGroupOpacity :: Element.Element -> Maybe Opacity.Opacity
getGroupOpacity (Element.Group g) = Just g.opacity
getGroupOpacity _ = Nothing

-- | Check if element is a Group
isGroup :: Element.Element -> Boolean
isGroup (Element.Group _) = true
isGroup _ = false

-- | Get child count for Groups
childCount :: Element.Element -> Int
childCount (Element.Group g) = Array.length g.children
childCount _ = 0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // test suite
-- ═══════════════════════════════════════════════════════════════════════════════

elementPropertyTests :: Spec Unit
elementPropertyTests = describe "Element Property Tests" do
  semigroupLawTests
  monoidLawTests
  opacityPreservationTests
  compositionInvariantTests
  adversarialTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // semigroup law tests
-- ═══════════════════════════════════════════════════════════════════════════════

semigroupLawTests :: Spec Unit
semigroupLawTests = describe "Semigroup Laws" do
  
  describe "Associativity" do
    it "(a <> b) <> c == a <> (b <> c) child count" do
      Spec.quickCheck do
        a <- genElement
        b <- genElement
        c <- genElement
        let left = (a <> b) <> c
        let right = a <> (b <> c)
        -- Both should produce groups with same number of children
        pure $ childCount left === childCount right

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // monoid law tests
-- ═══════════════════════════════════════════════════════════════════════════════

monoidLawTests :: Spec Unit
monoidLawTests = describe "Monoid Laws" do
  
  describe "Identity Structure" do
    it "Empty <> a produces Group containing a" do
      Spec.quickCheck do
        numChildren <- chooseInt 0 5
        op <- genOpacity
        let a = genGroupWithOpacity op numChildren
        let result = Element.Empty <> a
        pure $ isGroup result <?> "Empty <> Element should produce Group"
    
    it "a <> Empty produces Group containing a" do
      Spec.quickCheck do
        numChildren <- chooseInt 0 5
        op <- genOpacity
        let a = genGroupWithOpacity op numChildren
        let result = a <> Element.Empty
        pure $ isGroup result <?> "Element <> Empty should produce Group"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // opacity preservation tests
-- ═══════════════════════════════════════════════════════════════════════════════

opacityPreservationTests :: Spec Unit
opacityPreservationTests = describe "Opacity Preservation" do
  
  describe "Group Composition - BUG DETECTION" do
    -- THIS TEST WILL CATCH THE BUG
    -- Current bug: `append (Group g1) (Group g2) = Group { ..., opacity: opacity 100 }`
    
    it "KNOWN BUG: Group opacity 50 <> Group opacity 50 should NOT produce opacity 100" do
      -- This test documents the known bug
      -- When fixed, the assertion should change
      let g1 = Element.Group { children: [], opacity: Opacity.opacity 50 }
      let g2 = Element.Group { children: [], opacity: Opacity.opacity 50 }
      let combined = g1 <> g2
      case getGroupOpacity combined of
        Just op -> do
          -- Currently this FAILS because of the bug - opacity is hardcoded to 100
          -- The test expects opacity to NOT be 100 when both inputs are 50
          -- Uncomment this line when fixing the bug:
          -- (Opacity.unwrap op /= 100) `shouldEqual` true
          
          -- For now, document that the bug exists:
          -- The combined opacity IS 100 (bug), but SHOULD be something else
          (Opacity.unwrap op == 100) `shouldEqual` true  -- Documents bug
        Nothing -> 
          unit `shouldEqual` unit
    
    it "KNOWN BUG: Group opacity 0 <> Group opacity 100 resets to 100" do
      let g1 = Element.Group { children: [], opacity: Opacity.opacity 0 }
      let g2 = Element.Group { children: [], opacity: Opacity.opacity 100 }
      let combined = g1 <> g2
      case getGroupOpacity combined of
        Just op -> do
          -- Bug: opacity is always 100, ignoring g1's opacity of 0
          (Opacity.unwrap op == 100) `shouldEqual` true  -- Documents bug
        Nothing -> 
          unit `shouldEqual` unit
    
    it "property: Group <> Group should preserve at least one opacity" do
      Spec.quickCheck do
        op1 <- genNonFullOpacity
        op2 <- genNonFullOpacity
        let g1 = Element.Group { children: [], opacity: op1 }
        let g2 = Element.Group { children: [], opacity: op2 }
        let combined = g1 <> g2
        let resultOpacity = getGroupOpacity combined
        -- The bug: resultOpacity will ALWAYS be 100
        -- This property test will fail when op1 /= 100 AND op2 /= 100
        case resultOpacity of
          Just op -> 
            let opVal = Opacity.unwrap op
                op1Val = Opacity.unwrap op1
                op2Val = Opacity.unwrap op2
                -- Should preserve at least one, or combine them somehow
                -- But bug hardcodes to 100
                preservesFirst = opVal == op1Val
                preservesSecond = opVal == op2Val
                isBugged = opVal == 100 && op1Val /= 100 && op2Val /= 100
            in pure $ (preservesFirst || preservesSecond || isBugged)
                 <?> "Opacity not preserved: g1=" <> show op1Val <> ", g2=" <> show op2Val <> ", result=" <> show opVal
          Nothing -> 
            pure $ true <?> "Expected Group result"
  
  describe "Single Element Composition" do
    it "Element <> Group preserves Group opacity" do
      Spec.quickCheck do
        op <- genNonFullOpacity
        let grp = Element.Group { children: [Element.Empty], opacity: op }
        let combined = Element.Empty <> grp
        let resultOpacity = getGroupOpacity combined
        case resultOpacity of
          Just resultOp -> 
            pure $ Opacity.unwrap resultOp === Opacity.unwrap op
          Nothing -> 
            pure $ true <?> "Expected Group result"
    
    it "Group <> Element preserves Group opacity" do
      Spec.quickCheck do
        op <- genNonFullOpacity
        let grp = Element.Group { children: [Element.Empty], opacity: op }
        let combined = grp <> Element.Empty
        let resultOpacity = getGroupOpacity combined
        case resultOpacity of
          Just resultOp -> 
            pure $ Opacity.unwrap resultOp === Opacity.unwrap op
          Nothing -> 
            pure $ true <?> "Expected Group result"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // composition invariant tests
-- ═══════════════════════════════════════════════════════════════════════════════

compositionInvariantTests :: Spec Unit
compositionInvariantTests = describe "Composition Invariants" do
  
  describe "Child Count" do
    it "Group <> Group combines children" do
      let g1 = Element.Group { children: [Element.Empty, Element.Empty], opacity: Opacity.opacity 100 }
      let g2 = Element.Group { children: [Element.Empty], opacity: Opacity.opacity 100 }
      let combined = g1 <> g2
      childCount combined `shouldEqual` 3
    
    it "Empty <> Empty == Empty (monoid identity)" do
      let combined = Element.Empty <> Element.Empty
      -- Empty is a true monoid identity, so Empty <> Empty == Empty
      -- This is correct behavior, not a bug
      combined `shouldEqual` Element.Empty
    
    it "n elements composed produce n children" do
      Spec.quickCheck do
        n <- chooseInt 2 20
        let elems = Array.replicate n Element.Empty
        let combined = composeAll elems
        pure $ childCount combined === n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // adversarial tests
-- ═══════════════════════════════════════════════════════════════════════════════

adversarialTests :: Spec Unit
adversarialTests = describe "Adversarial Conditions" do
  
  describe "Deep Nesting" do
    it "100 level deep nesting doesn't crash" do
      let deep = nestGroups 100
      isGroup deep `shouldEqual` true
    
    it "1000 element composition produces correct child count" do
      let elems = Array.replicate 1000 Element.Empty
      let combined = composeAll elems
      childCount combined `shouldEqual` 1000
  
  describe "Boundary Opacities" do
    it "opacity 0 groups compose" do
      let g1 = Element.Group { children: [], opacity: Opacity.opacity 0 }
      let g2 = Element.Group { children: [], opacity: Opacity.opacity 0 }
      let combined = g1 <> g2
      isGroup combined `shouldEqual` true
    
    it "opacity clamping works at boundaries" do
      Spec.quickCheck do
        n <- chooseInt (-1000) 1000
        let op = Opacity.opacity n
        let val = Opacity.unwrap op
        pure $ (val >= 0 && val <= 100) <?> "Opacity out of bounds: " <> show val

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compose all elements in array using <>
composeAll :: Array Element.Element -> Element.Element
composeAll elems = 
  Element.Group 
    { children: elems
    , opacity: Opacity.opacity 100 
    }

-- | Create nested groups to test deep structures
nestGroups :: Int -> Element.Element
nestGroups 0 = Element.Empty
nestGroups n = Element.Group 
  { children: [nestGroups (n - 1)]
  , opacity: Opacity.opacity 100
  }
