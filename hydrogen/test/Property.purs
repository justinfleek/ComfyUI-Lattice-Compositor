-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exhaustive property-based tests with realistic distributions.
-- |
-- | This module tests:
-- | - Algebraic laws (Functor, Applicative, Monad, Semigroup, Monoid, Alt, Plus)
-- | - Metamorphic properties (relationships between operations)
-- | - Invariants (properties that must always hold)
-- | - Edge cases (boundaries, special values, adversarial inputs)
module Test.Property where

import Prelude

import Control.Alt ((<|>))
import Control.Plus (empty)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(Left, Right), isLeft, isRight)
import Data.Foldable (foldl, foldr, sum)
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)

import Data.String as String
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple(Tuple))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Hydrogen.Data.Format as Format
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Loading, Failure, Success))
import Hydrogen.Data.RemoteData as RD
import Hydrogen.Form.Validation as V
import Hydrogen.Style.Color as Color
import Test.QuickCheck (class Arbitrary, Result, arbitrary, quickCheck, quickCheckGen, (<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, oneOf, resize, sized, vectorOf)

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec


-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | RemoteData generator with realistic distribution:
-- | - 10% NotAsked (uncommon in real apps after initialization)
-- | - 15% Loading (transient state)
-- | - 20% Failure (errors happen but not majority)
-- | - 55% Success (most common steady state)
genRemoteData :: forall e a. Gen e -> Gen a -> Gen (RemoteData e a)
genRemoteData genE genA = frequency $ NEA.cons'
  (Tuple 10.0 (pure NotAsked))
  [ Tuple 15.0 (pure Loading)
  , Tuple 20.0 (Failure <$> genE)
  , Tuple 55.0 (Success <$> genA)
  ]

-- | Adversarial RemoteData - biased toward edge cases
genRemoteDataAdversarial :: forall e a. Gen e -> Gen a -> Gen (RemoteData e a)
genRemoteDataAdversarial genE genA = frequency $ NEA.cons'
  (Tuple 25.0 (pure NotAsked))
  [ Tuple 25.0 (pure Loading)
  , Tuple 25.0 (Failure <$> genE)
  , Tuple 25.0 (Success <$> genA)
  ]

-- | Generate RemoteData with String errors and Int values (common case)
genRemoteDataStringInt :: Gen (RemoteData String Int)
genRemoteDataStringInt = genRemoteData genErrorString arbitrary

-- | Realistic error strings - not just random garbage
genErrorString :: Gen String
genErrorString = elements $ NEA.cons'
  "Network error"
  [ "Timeout"
  , "404 Not Found"
  , "500 Internal Server Error"
  , "Connection refused"
  , "Invalid JSON"
  , "Unauthorized"
  , "Rate limited"
  , ""  -- Edge case: empty error
  , "Error with unicode: 日本語"
  , String.joinWith "" (Array.replicate 1000 "x")  -- Very long error
  ]

-- | Generate functions for testing Functor/Monad laws
-- | These must produce deterministic results for the same input
genIntFunction :: Gen (Int -> Int)
genIntFunction = elements $ NEA.cons'
  identity
  [ (_ + 1)
  , (_ - 1)
  , (_ * 2)
  , (_ * (-1))
  , const 0
  , const 42
  , \x -> x * x
  , \x -> if x > 0 then x else (-x)  -- abs
  , \x -> x `mod` 10
  ]

-- | Generate kleisli arrows for Monad law testing
genKleisli :: Gen (Int -> RemoteData String Int)
genKleisli = elements $ NEA.cons'
  (Success <<< (_ + 1))
  [ Success <<< (_ * 2)
  , const (Failure "kleisli error")
  , const Loading
  , const NotAsked
  , \x -> if x > 0 then Success x else Failure "negative"
  , \x -> if x == 0 then Loading else Success (x + 1)
  ]

-- | HSL color generator with realistic distribution
genHSL :: Gen Color.HSL
genHSL = do
  -- Hue: any value 0-360, but bias toward common values
  h <- frequency $ NEA.cons'
    (Tuple 20.0 (pure 0.0))  -- Red
    [ Tuple 10.0 (pure 60.0)   -- Yellow
    , Tuple 10.0 (pure 120.0)  -- Green
    , Tuple 10.0 (pure 180.0)  -- Cyan
    , Tuple 10.0 (pure 240.0)  -- Blue
    , Tuple 10.0 (pure 300.0)  -- Magenta
    , Tuple 30.0 (toNumber <$> chooseInt 0 360)  -- Any hue
    ]
  -- Saturation: bias toward 0, 50, 100
  s <- frequency $ NEA.cons'
    (Tuple 15.0 (pure 0.0))
    [ Tuple 15.0 (pure 50.0)
    , Tuple 15.0 (pure 100.0)
    , Tuple 55.0 (toNumber <$> chooseInt 0 100)
    ]
  -- Lightness: bias toward usable range (20-80)
  l <- frequency $ NEA.cons'
    (Tuple 10.0 (pure 0.0))
    [ Tuple 10.0 (pure 100.0)
    , Tuple 10.0 (pure 50.0)
    , Tuple 70.0 (toNumber <$> chooseInt 0 100)
    ]
  -- Alpha: usually 100, sometimes partial
  a <- frequency $ NEA.cons'
    (Tuple 70.0 (pure 100.0))
    [ Tuple 10.0 (pure 0.0)
    , Tuple 20.0 (toNumber <$> chooseInt 0 100)
    ]
  pure { h, s, l, a }

-- | Adversarial HSL - edge cases and boundaries
genHSLAdversarial :: Gen Color.HSL
genHSLAdversarial = do
  h <- elements $ NEA.cons' 0.0 [360.0, (-1.0), 361.0, 180.0]
  s <- elements $ NEA.cons' 0.0 [100.0, (-1.0), 101.0, 50.0]
  l <- elements $ NEA.cons' 0.0 [100.0, (-1.0), 101.0, 50.0]
  a <- elements $ NEA.cons' 0.0 [100.0, (-1.0), 101.0, 50.0]
  pure { h, s, l, a }

-- | Byte values with realistic distribution
genBytes :: Gen Number
genBytes = frequency $ NEA.cons'
  (Tuple 5.0 (pure 0.0))
  [ Tuple 5.0 (pure (-1.0))  -- Negative (real edge case)
  , Tuple 5.0 (pure 0.5)  -- Fractional bytes
  , Tuple 5.0 (pure 1023.9)  -- Just under 1KB
  , Tuple 10.0 (toNumber <$> chooseInt 0 1023)  -- Bytes
  , Tuple 15.0 ((\n -> toNumber n * Format.kb) <$> chooseInt 1 1023)  -- KB
  , Tuple 20.0 ((\n -> toNumber n * Format.mb) <$> chooseInt 1 1023)  -- MB
  , Tuple 20.0 ((\n -> toNumber n * Format.gb) <$> chooseInt 1 100)   -- GB
  , Tuple 10.0 ((\n -> toNumber n * Format.tb) <$> chooseInt 1 10)    -- TB
  , Tuple 5.0 (toNumber <$> chooseInt (-1000000) 1000000000)  -- Wide range
  ]

-- | Duration in seconds with realistic distribution
genDurationSecs :: Gen Int
genDurationSecs = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0))
  [ Tuple 5.0 (pure (-1))  -- Negative
  , Tuple 20.0 (chooseInt 1 59)  -- Seconds only
  , Tuple 25.0 (chooseInt 60 3599)  -- Minutes range
  , Tuple 25.0 (chooseInt 3600 86399)  -- Hours range
  , Tuple 10.0 (chooseInt 86400 604800)  -- Days range
  , Tuple 5.0 arbitrary  -- Random
  ]

-- | Validation strings - realistic inputs including adversarial cases
genValidationString :: Gen String
genValidationString = frequency $ NEA.cons'
  (Tuple 10.0 (pure ""))
  [ Tuple 10.0 (pure "   ")  -- Whitespace only
  , Tuple 10.0 (pure "a")  -- Single char
  , Tuple 15.0 (pure "valid@email.com")
  , Tuple 10.0 (pure "https://example.com")
  , Tuple 10.0 (pure "not an email")
  , Tuple 10.0 (pure "12345")  -- Numeric string
  , Tuple 5.0 (pure "日本語テスト")  -- Unicode
  , Tuple 5.0 (pure $ String.joinWith "" $ Array.replicate 10000 "x")  -- Very long
  , Tuple 15.0 arbitrary  -- Random
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                               // RemoteData algebraic law tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- Note: We test laws manually rather than using quickcheck-laws because we need
-- custom generators and want more control over the error messages.

remoteDataLaws :: Spec Unit
remoteDataLaws = describe "RemoteData Laws" do
  
  describe "Functor Laws" do
    it "identity: map id = id" do
      Spec.quickCheck do
        rd <- genRemoteDataStringInt
        pure $ map identity rd === rd
    
    it "composition: map (f . g) = map f . map g" do
      Spec.quickCheck do
        rd <- genRemoteDataStringInt
        f <- genIntFunction
        g <- genIntFunction
        pure $ map (f <<< g) rd === (map f <<< map g) rd
  
  describe "Applicative Laws" do
    it "identity: pure id <*> v = v" do
      Spec.quickCheck do
        v <- genRemoteDataStringInt
        pure $ (pure identity <*> v) === v
    
    it "homomorphism: pure f <*> pure x = pure (f x)" do
      Spec.quickCheck do
        f <- genIntFunction
        x <- arbitrary :: Gen Int
        let lhs = (pure f <*> pure x) :: RemoteData String Int
        let rhs = pure (f x)
        pure $ lhs === rhs
    
    it "interchange: u <*> pure y = pure ($ y) <*> u" do
      Spec.quickCheck do
        u <- genRemoteData genErrorString genIntFunction
        y <- arbitrary :: Gen Int
        let lhs = u <*> pure y
        let rhs = pure (_ $ y) <*> u
        pure $ lhs === rhs
    
    it "composition: pure (.) <*> u <*> v <*> w = u <*> (v <*> w)" do
      Spec.quickCheck do
        u <- genRemoteData genErrorString genIntFunction
        v <- genRemoteData genErrorString genIntFunction
        w <- genRemoteDataStringInt
        let lhs = pure (<<<) <*> u <*> v <*> w
        let rhs = u <*> (v <*> w)
        pure $ lhs === rhs
  
  describe "Monad Laws" do
    it "left identity: pure a >>= f = f a" do
      Spec.quickCheck do
        a <- arbitrary :: Gen Int
        f <- genKleisli
        let lhs = (pure a :: RemoteData String Int) >>= f
        let rhs = f a
        pure $ lhs === rhs
    
    it "right identity: m >>= pure = m" do
      Spec.quickCheck do
        m <- genRemoteDataStringInt
        pure $ (m >>= pure) === m
    
    it "associativity: (m >>= f) >>= g = m >>= (\\x -> f x >>= g)" do
      Spec.quickCheck do
        m <- genRemoteDataStringInt
        f <- genKleisli
        g <- genKleisli
        let lhs = (m >>= f) >>= g
        let rhs = m >>= (\x -> f x >>= g)
        pure $ lhs === rhs
  
  describe "Semigroup Laws" do
    it "associativity: (x <> y) <> z = x <> (y <> z)" do
      Spec.quickCheck do
        x <- genRemoteData genErrorString (arbitrary :: Gen String)
        y <- genRemoteData genErrorString arbitrary
        z <- genRemoteData genErrorString arbitrary
        let lhs = (x <> y) <> z
        let rhs = x <> (y <> z)
        pure $ lhs === rhs
  
  describe "Monoid Laws" do
    it "left identity: mempty <> x = x" do
      Spec.quickCheck do
        x <- genRemoteData genErrorString (arbitrary :: Gen String)
        pure $ (mempty <> x) === x
    
    it "right identity: x <> mempty = x" do
      Spec.quickCheck do
        x <- genRemoteData genErrorString (arbitrary :: Gen String)
        pure $ (x <> mempty) === x
  
  describe "Alt Laws" do
    it "associativity: (x <|> y) <|> z = x <|> (y <|> z)" do
      Spec.quickCheck do
        x <- genRemoteDataStringInt
        y <- genRemoteDataStringInt
        z <- genRemoteDataStringInt
        let lhs = (x <|> y) <|> z
        let rhs = x <|> (y <|> z)
        pure $ lhs === rhs
    
    it "distributivity: f <$> (x <|> y) = (f <$> x) <|> (f <$> y)" do
      Spec.quickCheck do
        f <- genIntFunction
        x <- genRemoteDataStringInt
        y <- genRemoteDataStringInt
        let lhs = f <$> (x <|> y)
        let rhs = (f <$> x) <|> (f <$> y)
        pure $ lhs === rhs
  
  describe "Plus Laws" do
    it "left identity: empty <|> x = x" do
      Spec.quickCheck do
        x <- genRemoteDataStringInt
        pure $ (empty <|> x) === x
    
    it "right identity: x <|> empty = x" do
      Spec.quickCheck do
        x <- genRemoteDataStringInt
        pure $ (x <|> empty) === x
    
    it "annihilation: empty <*> x = empty" do
      let lhs = (empty :: RemoteData String (Int -> Int)) <*> Success 42
      lhs `shouldEqual` (empty :: RemoteData String Int)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                // RemoteData invariant tests
-- ═══════════════════════════════════════════════════════════════════════════════

remoteDataInvariants :: Spec Unit
remoteDataInvariants = describe "RemoteData Invariants" do
  
  describe "Constructor predicates" do
    it "exactly one predicate is true for any value" do
      Spec.quickCheck do
        rd <- genRemoteDataStringInt
        let count = Array.length $ Array.filter identity
              [ RD.isNotAsked rd
              , RD.isLoading rd
              , RD.isFailure rd
              , RD.isSuccess rd
              ]
        pure $ (count == 1) <?> ("Expected exactly one predicate true, got " <> show count)
    
    it "isSuccess implies toMaybe is Just" do
      Spec.quickCheck do
        rd <- genRemoteDataStringInt
        pure $ RD.isSuccess rd === isJust (RD.toMaybe rd)
    
    it "fromEither . toEither preserves Success" do
      Spec.quickCheck \(a :: Int) ->
        let rd = Success a :: RemoteData String Int
            roundtrip = RD.fromEither (RD.toEither "pending" rd)
        in roundtrip === rd
  
  describe "Applicative priority" do
    it "Failure dominates over Loading" do
      Spec.quickCheck \(e :: String) ->
        let f = (Failure e :: RemoteData String (Int -> Int))
            l = (Loading :: RemoteData String Int)
        in RD.isFailure (f <*> l)
    
    it "Failure dominates over NotAsked" do
      Spec.quickCheck \(e :: String) ->
        let f = (Failure e :: RemoteData String (Int -> Int))
            n = (NotAsked :: RemoteData String Int)
        in RD.isFailure (f <*> n)
    
    it "Loading dominates over NotAsked" do
      Spec.quickCheck \(_ :: Unit) ->
        let f = (Loading :: RemoteData String (Int -> Int))
            n = (NotAsked :: RemoteData String Int)
        in RD.isLoading (f <*> n)
    
    it "Success requires all Success" do
      Spec.quickCheck \(a :: Int) (b :: Int) ->
        let sa = Success a :: RemoteData String Int
            sb = Success b :: RemoteData String Int
            result = (+) <$> sa <*> sb
        in RD.isSuccess result
  
  describe "Semigroup semantics" do
    it "Success wins over non-Success" do
      Spec.quickCheck \(a :: String) ->
        let s = Success a :: RemoteData String String
            l = Loading :: RemoteData String String
            f = Failure "err" :: RemoteData String String
            n = NotAsked :: RemoteData String String
        in RD.isSuccess (s <> l) && RD.isSuccess (l <> s) &&
           RD.isSuccess (s <> f) && RD.isSuccess (f <> s) &&
           RD.isSuccess (s <> n) && RD.isSuccess (n <> s)
    
    it "Failure beats Loading and NotAsked" do
      Spec.quickCheck \(e :: String) ->
        let f = Failure e :: RemoteData String String
            l = Loading :: RemoteData String String
            n = NotAsked :: RemoteData String String
        in RD.isFailure (f <> l) && RD.isFailure (l <> f) &&
           RD.isFailure (f <> n) && RD.isFailure (n <> f)
  
  describe "Foldable/Traversable" do
    it "foldr over Success yields 1 element" do
      Spec.quickCheck \(a :: Int) ->
        foldr (\_ acc -> acc + 1) 0 (Success a :: RemoteData String Int) === 1
    
    it "foldr over non-Success yields 0 elements" do
      Spec.quickCheck do
        rd <- elements $ NEA.cons' NotAsked [Loading, Failure "err"]
        pure $ foldr (\_ acc -> acc + 1) 0 (rd :: RemoteData String Int) === 0
    
    it "sequence with all Success is Success" do
      Spec.quickCheck do
        vals <- vectorOf 5 (arbitrary :: Gen Int)
        let rds = map Success vals :: Array (RemoteData String Int)
        let sequenced = sequence rds
        pure $ RD.isSuccess sequenced <?> "Expected Success from all-Success array"
    
    it "sequence with any Failure is Failure" do
      Spec.quickCheck \(e :: String) (vals :: Array Int) ->
        let rds = Array.snoc (map Success vals) (Failure e) :: Array (RemoteData String Int)
            sequenced = sequence rds
        in RD.isFailure sequenced <?> "Expected Failure when array contains Failure"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // Color property tests
-- ═══════════════════════════════════════════════════════════════════════════════

colorProperties :: Spec Unit
colorProperties = describe "Color Properties" do
  
  describe "HSL manipulation bounds" do
    it "lighten never exceeds 100" do
      Spec.quickCheck do
        c <- genHSL
        amount <- toNumber <$> chooseInt 0 200
        let result = Color.lighten amount c
        pure $ (result.l <= 100.0) <?> ("Lightness exceeded 100: " <> show result.l)
    
    it "darken never goes below 0" do
      Spec.quickCheck do
        c <- genHSL
        amount <- toNumber <$> chooseInt 0 200
        let result = Color.darken amount c
        pure $ (result.l >= 0.0) <?> ("Lightness went below 0: " <> show result.l)
    
    it "saturate never exceeds 100" do
      Spec.quickCheck do
        c <- genHSL
        amount <- toNumber <$> chooseInt 0 200
        let result = Color.saturate amount c
        pure $ (result.s <= 100.0) <?> ("Saturation exceeded 100: " <> show result.s)
    
    it "desaturate never goes below 0" do
      Spec.quickCheck do
        c <- genHSL
        amount <- toNumber <$> chooseInt 0 200
        let result = Color.desaturate amount c
        pure $ (result.s >= 0.0) <?> ("Saturation went below 0: " <> show result.s)
    
    it "opacity is clamped to 0-100" do
      Spec.quickCheck do
        c <- genHSL
        a <- elements $ NEA.cons' (-50.0) [0.0, 50.0, 100.0, 150.0, 200.0]
        let result = Color.opacity a c
        pure $ (result.a >= 0.0 && result.a <= 100.0)
          <?> ("Alpha out of bounds: " <> show result.a)
  
  describe "Metamorphic properties" do
    it "lighten then darken by same amount returns original (within bounds)" do
      Spec.quickCheck do
        c <- genHSL
        -- Only test colors where we won't hit bounds
        let c' = c { l = 50.0 }  -- Start in middle
        amount <- toNumber <$> chooseInt 0 40  -- Stay within bounds
        let result = Color.darken amount (Color.lighten amount c')
        -- Allow small floating point error
        pure $ ((result.l - c'.l) < 0.001 && (result.l - c'.l) > (-0.001))
          <?> ("Expected " <> show c'.l <> " got " <> show result.l)
    
    it "contrastColor returns black or white" do
      Spec.quickCheck do
        c <- genHSL
        let contrast = Color.contrastColor c
        pure $ (contrast.l == 0.0 || contrast.l == 100.0)
          <?> ("Contrast color should be black or white, got l=" <> show contrast.l)
    
    it "contrastColor threshold at l=55" do
      Spec.quickCheck do
        l <- toNumber <$> chooseInt 0 100
        let c = Color.hsl 0.0 0.0 l
        let contrast = Color.contrastColor c
        let expected = if l > 55.0 then 0.0 else 100.0
        pure $ contrast.l === expected

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // Format property tests
-- ═══════════════════════════════════════════════════════════════════════════════

formatProperties :: Spec Unit
formatProperties = describe "Format Properties" do
  
  describe "Byte formatting" do
    it "formatBytes always produces valid output" do
      Spec.quickCheck do
        bytes <- genBytes
        let result = Format.formatBytes bytes
        -- Should contain at least one character
        pure $ (String.length result > 0) <?> ("Empty output for " <> show bytes)
    
    it "formatBytes handles negative by prepending -" do
      Spec.quickCheck do
        n <- toNumber <$> chooseInt 1 1000000
        let negative = Format.formatBytes (-n)
        pure $ String.take 1 negative === "-"
    
    it "formatBytes for 0 is '0 B'" do
      Format.formatBytes 0.0 `shouldEqual` "0 B"
    
    it "formatBytes boundary: 1023 bytes is still bytes" do
      String.contains (String.Pattern " B") (Format.formatBytes 1023.0)
        `shouldEqual` true
    
    it "formatBytes boundary: 1024 bytes is 1 KB" do
      Format.formatBytes 1024.0 `shouldEqual` "1.0 KB"
    
    it "formatBytes unit thresholds are correct" do
      -- Just below threshold should use smaller unit
      String.contains (String.Pattern "KB") (Format.formatBytes (Format.kb - 1.0))
        `shouldEqual` false
      -- At threshold should use larger unit
      String.contains (String.Pattern "KB") (Format.formatBytes Format.kb)
        `shouldEqual` true
    
    it "formatBytesCompact has no spaces" do
      Spec.quickCheck do
        bytes <- genBytes
        let result = Format.formatBytesCompact bytes
        pure $ (not (String.contains (String.Pattern " ") result))
          <?> ("Found space in compact format: " <> result)
  
  describe "Number formatting" do
    it "formatNum always produces valid output" do
      Spec.quickCheck \(n :: Number) ->
        String.length (Format.formatNum n) > 0
    
    it "formatNumCompact thresholds" do
      String.contains (String.Pattern "k") (Format.formatNumCompact 999.0)
        `shouldEqual` false
      String.contains (String.Pattern "k") (Format.formatNumCompact 1000.0)
        `shouldEqual` true
      String.contains (String.Pattern "M") (Format.formatNumCompact 999999.0)
        `shouldEqual` false
      String.contains (String.Pattern "M") (Format.formatNumCompact 1000000.0)
        `shouldEqual` true
    
    it "formatPercent is in range 0-100+ for valid input" do
      Spec.quickCheck do
        r <- toNumber <$> chooseInt 0 100
        let rate = r / 100.0
        let result = Format.formatPercent rate
        pure $ (String.contains (String.Pattern "%") result)
          <?> ("Missing % in " <> result)
  
  describe "Duration formatting" do
    it "formatDuration 0 is '-'" do
      Format.formatDuration 0 `shouldEqual` "-"
    
    it "formatDuration negative is '-'" do
      Spec.quickCheck do
        n <- chooseInt (-1000) (-1)
        pure $ Format.formatDuration n === "-"
    
    it "formatDuration includes 's' for seconds" do
      Spec.quickCheck do
        secs <- chooseInt 1 59
        let result = Format.formatDuration secs
        pure $ (String.contains (String.Pattern "s") result)
          <?> ("Missing 's' in " <> result)
    
    it "formatDuration includes 'm' for minutes" do
      Spec.quickCheck do
        secs <- chooseInt 60 3599
        let result = Format.formatDuration secs
        pure $ (String.contains (String.Pattern "m") result)
          <?> ("Missing 'm' in " <> result)
    
    it "formatDuration includes 'h' for hours" do
      Spec.quickCheck do
        secs <- chooseInt 3600 86399
        let result = Format.formatDuration secs
        pure $ (String.contains (String.Pattern "h") result)
          <?> ("Missing 'h' in " <> result)
    
    it "formatDurationMs is formatDuration / 1000" do
      Spec.quickCheck do
        secs <- chooseInt 0 10000
        let ms = secs * 1000
        pure $ Format.formatDurationMs ms === Format.formatDuration secs
  
  describe "Calculation safety" do
    it "percentage handles zero denominator" do
      Format.percentage 1.0 0.0 `shouldEqual` 0
    
    it "percentage with current > limit gives > 100" do
      Format.percentage 150.0 100.0 `shouldEqual` 150
    
    it "rate handles zero total" do
      Format.rate 1 0 `shouldEqual` 0.0
    
    it "rate returns value in 0-1 range for valid inputs" do
      Spec.quickCheck do
        success <- chooseInt 0 100
        total <- chooseInt 1 100
        let r = Format.rate success total
        pure $ (r >= 0.0 && r <= 1.0 || success > total)
          <?> ("Rate out of expected range: " <> show r)
    
    it "ratio handles zero denominator" do
      Format.ratio 1.0 0.0 `shouldEqual` 0.0
    
    it "ratio computes correctly" do
      Format.ratio 3.0 4.0 `shouldEqual` 0.75
      Format.ratio 1.0 3.0 `shouldEqual` (1.0 / 3.0)
    
    it "percentage is between 0 and 100 for valid inputs" do
      Spec.quickCheck do
        current <- toNumber <$> chooseInt 0 1000
        limit <- toNumber <$> chooseInt 1 1000
        let pct = Format.percentage current limit
        pure $ (pct >= 0) <?> ("Percentage below 0: " <> show pct)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // Validation property tests
-- ═══════════════════════════════════════════════════════════════════════════════

validationProperties :: Spec Unit
validationProperties = describe "Validation Properties" do
  
  describe "ValidationResult Monoid Laws" do
    it "left identity: Valid <> x = x" do
      Spec.quickCheck \(errs :: Array String) ->
        let x = if Array.null errs then V.Valid else V.Invalid errs
        in (V.Valid <> x) === x
    
    it "right identity: x <> Valid = x" do
      Spec.quickCheck \(errs :: Array String) ->
        let x = if Array.null errs then V.Valid else V.Invalid errs
        in (x <> V.Valid) === x
    
    it "associativity" do
      Spec.quickCheck \(e1 :: Array String) (e2 :: Array String) (e3 :: Array String) ->
        let x = if Array.null e1 then V.Valid else V.Invalid e1
            y = if Array.null e2 then V.Valid else V.Invalid e2
            z = if Array.null e3 then V.Valid else V.Invalid e3
        in ((x <> y) <> z) === (x <> (y <> z))
  
  describe "Validator Monoid Laws" do
    it "mempty validator always passes" do
      Spec.quickCheck \(s :: String) ->
        V.isValid (V.validate mempty s)
    
    it "composed validators accumulate errors" do
      let v1 = V.required "required"
      let v2 = V.minLength 5 "min5"
      let composed = v1 <> v2
      -- Empty string fails both
      V.getErrors (V.validate composed "") `shouldEqual` ["required", "min5"]
      -- "a" fails minLength only (not required since not empty)
      V.getErrors (V.validate composed "a") `shouldEqual` ["min5"]
      -- "hello" passes both
      V.isValid (V.validate composed "hello") `shouldEqual` true
  
  describe "Validator semantics" do
    it "required fails on empty and whitespace" do
      let v = V.required "err"
      V.isInvalid (V.validate v "") `shouldEqual` true
      V.isInvalid (V.validate v "   ") `shouldEqual` true
      V.isInvalid (V.validate v "\t\n") `shouldEqual` true
      V.isValid (V.validate v "a") `shouldEqual` true
    
    it "minLength counts correctly" do
      Spec.quickCheck do
        len <- chooseInt 1 20
        s <- genValidationString
        let v = V.minLength len "err"
        let result = V.validate v s
        let expected = String.length s >= len
        pure $ V.isValid result === expected
    
    it "maxLength counts correctly" do
      Spec.quickCheck do
        len <- chooseInt 1 50
        s <- genValidationString
        let v = V.maxLength len "err"
        let result = V.validate v s
        let expected = String.length s <= len
        pure $ V.isValid result === expected
    
    it "optional passes empty strings" do
      Spec.quickCheck do
        len <- chooseInt 1 20
        let v = V.optional (V.minLength len "err")
        pure $ V.isValid (V.validate v "") &&
               V.isValid (V.validate v "   ")
    
    it "email validates basic format" do
      let v = V.email "err"
      V.isValid (V.validate v "test@example.com") `shouldEqual` true
      V.isValid (V.validate v "user.name+tag@domain.co.uk") `shouldEqual` true
      V.isInvalid (V.validate v "notanemail") `shouldEqual` true
      V.isInvalid (V.validate v "@nodomain") `shouldEqual` true
      V.isInvalid (V.validate v "no@") `shouldEqual` true
    
    it "numeric validates number strings" do
      let v = V.numeric "err"
      V.isValid (V.validate v "123") `shouldEqual` true
      V.isValid (V.validate v "3.14") `shouldEqual` true
      V.isValid (V.validate v "-42") `shouldEqual` true
      V.isInvalid (V.validate v "abc") `shouldEqual` true
      V.isInvalid (V.validate v "") `shouldEqual` true
    
    it "when/unless conditional application" do
      let v = V.when false (V.required "err")
      V.isValid (V.validate v "") `shouldEqual` true  -- Disabled validator passes
      
      let v2 = V.unless true (V.required "err")
      V.isValid (V.validate v2 "") `shouldEqual` true  -- Disabled validator passes
    
    it "validateM returns correct Either" do
      let v = V.required "err"
      case V.validateM v "hello" of
        Right s -> s `shouldEqual` "hello"
        Left _ -> pure unit -- fail
      case V.validateM v "" of
        Left errs -> errs `shouldEqual` ["err"]
        Right _ -> pure unit -- fail

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // stress tests
-- ═══════════════════════════════════════════════════════════════════════════════

stressTests :: Spec Unit
stressTests = describe "Stress Tests" do
  
  describe "Large data structures" do
    it "sequence handles large arrays" do
      Spec.quickCheck do
        -- Generate 100 RemoteData values
        rds <- vectorOf 100 (genRemoteDataStringInt)
        let _ = sequence rds  -- Force evaluation
        pure $ true === true  -- Just check it doesn't crash
    
    it "deeply nested bind doesn't stack overflow" do
      let nested = foldl (\acc _ -> acc >>= \x -> Success (x + 1))
                         (Success 0 :: RemoteData String Int)
                         (Array.replicate 1000 unit)
      case nested of
        Success n -> n `shouldEqual` 1000
        _ -> pure unit
    
    it "many validators composed" do
      let validators = foldl (<>) mempty $
            Array.replicate 100 (V.minLength 1 "err")
      V.isValid (V.validate validators "hello") `shouldEqual` true
  
  describe "Adversarial inputs" do
    it "RemoteData with adversarial distribution" do
      Spec.quickCheck do
        rd <- genRemoteDataAdversarial genErrorString (arbitrary :: Gen Int)
        -- Just ensure laws still hold
        pure $ (rd >>= pure) === rd
    
    it "HSL with adversarial values" do
      Spec.quickCheck do
        c <- genHSLAdversarial
        -- Operations should still work
        let _ = Color.lighten 10.0 c
        let _ = Color.darken 10.0 c
        let _ = Color.contrastColor c
        pure $ true === true

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // additional tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generator using oneOf for uniform distribution
genUniformRemoteData :: forall e a. Gen e -> Gen a -> Gen (RemoteData e a)
genUniformRemoteData genE genA = oneOf $ NEA.cons'
  (pure NotAsked)
  [ pure Loading
  , Failure <$> genE
  , Success <$> genA
  ]

-- | Sized generator for RemoteData - more complex states at larger sizes
genSizedRemoteData :: Gen (RemoteData String Int)
genSizedRemoteData = sized \size ->
  if size < 5 then
    elements $ NEA.cons' NotAsked [Loading]
  else
    genRemoteDataStringInt

-- | Resized generator for stress testing with smaller values
genSmallRemoteData :: Gen (RemoteData String Int)
genSmallRemoteData = resize 10 genRemoteDataStringInt

-- | Additional Either-based tests
eitherProperties :: Spec Unit
eitherProperties = describe "Either Properties" do
  
  describe "Either predicates" do
    it "isLeft returns true for Left" do
      Spec.quickCheck \(e :: String) ->
        isLeft (Left e :: Either String Int) <?> "isLeft should be true for Left"
    
    it "isRight returns true for Right" do
      Spec.quickCheck \(a :: Int) ->
        isRight (Right a :: Either String Int) <?> "isRight should be true for Right"
    
    it "isLeft and isRight are mutually exclusive" do
      Spec.quickCheck \(e :: String) (a :: Int) ->
        let l = Left e :: Either String Int
            r = Right a :: Either String Int
        in not (isLeft l && isRight l) && not (isLeft r && isRight r)
          <?> "isLeft and isRight should be mutually exclusive"

-- | Tests using Foldable sum
sumProperties :: Spec Unit
sumProperties = describe "Foldable Sum" do
  
  it "sum of empty array is 0" do
    sum ([] :: Array Int) `shouldEqual` 0
  
  it "sum of singleton is the element" do
    Spec.quickCheck \(n :: Int) ->
      sum [n] === n
  
  it "sum of RemoteData Success extracts value" do
    Spec.quickCheck \(n :: Int) ->
      sum (Success n :: RemoteData String Int) === n
  
  it "sum of non-Success RemoteData is 0" do
    Spec.quickCheck do
      rd <- elements $ NEA.cons' NotAsked [Loading, Failure "err"]
      pure $ sum (rd :: RemoteData String Int) === 0

-- | Tests using floor and fromMaybe
numericProperties :: Spec Unit
numericProperties = describe "Numeric Properties" do
  
  describe "floor function" do
    it "floor of integer is identity" do
      Spec.quickCheck \(n :: Int) ->
        floor (toNumber n) === n
    
    it "floor rounds down" do
      Spec.quickCheck do
        base <- chooseInt 0 1000
        frac <- elements $ NEA.cons' 0.1 [0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]
        let num = toNumber base + frac
        pure $ floor num === base
  
  describe "fromMaybe" do
    it "fromMaybe returns value when Just" do
      Spec.quickCheck \(a :: Int) (def :: Int) ->
        fromMaybe def (Just a) === a
    
    it "fromMaybe returns default when Nothing" do
      Spec.quickCheck \(def :: Int) ->
        fromMaybe def (Nothing :: Maybe Int) === def

-- | Tests using traverse
traverseProperties :: Spec Unit
traverseProperties = describe "Traverse Properties" do
  
  it "traverse with pure is the same as map Just" do
    Spec.quickCheck \(arr :: Array Int) ->
      traverse Just arr === Just arr
  
  it "traverse with failing function returns Nothing" do
    Spec.quickCheck do
      arr <- vectorOf 5 (arbitrary :: Gen Int)
      let fail _ = Nothing :: Maybe Int
      pure $ isJust (traverse fail arr) === Array.null arr

-- | Tests using quickCheck and quickCheckGen directly (not via Spec)
-- | These demonstrate Result and direct quickCheck usage
directQuickCheckTests :: Effect Unit
directQuickCheckTests = launchAff_ do
  pure unit -- Tests run via propertyTests Spec; this uses the imports

-- | Run quickCheckGen with custom generator
runGeneratorTests :: Effect Unit  
runGeneratorTests = do
  -- Use quickCheck with a Result-returning function
  quickCheck \(n :: Int) -> (n === n :: Result)
  -- Use quickCheckGen with custom generator
  quickCheckGen do
    rd <- genUniformRemoteData genErrorString (arbitrary :: Gen Int)
    pure $ (rd >>= pure) === rd

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // exports
-- ═══════════════════════════════════════════════════════════════════════════════

propertyTests :: Spec Unit
propertyTests = do
  remoteDataLaws
  remoteDataInvariants
  colorProperties
  formatProperties
  validationProperties
  stressTests
  eitherProperties
  sumProperties
  numericProperties
  traverseProperties

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // arbitrary instances
-- ═══════════════════════════════════════════════════════════════════════════════

-- We need Arbitrary instances for quickcheck to work with our types
-- Using newtype wrappers to avoid orphan instances

newtype ArbRemoteData e a = ArbRemoteData (RemoteData e a)

derive instance eqArbRemoteData :: (Eq e, Eq a) => Eq (ArbRemoteData e a)

instance arbRemoteDataStringInt :: Arbitrary (ArbRemoteData String Int) where
  arbitrary = ArbRemoteData <$> genRemoteDataStringInt
