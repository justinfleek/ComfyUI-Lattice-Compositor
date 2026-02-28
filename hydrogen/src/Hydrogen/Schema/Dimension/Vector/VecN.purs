-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // vector // vecn
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | N-dimensional vector for arbitrary dimensions.
-- |
-- | Used for:
-- | - Latent space embeddings (512, 768, 1024+ dimensions)
-- | - Neural network activations
-- | - High-dimensional optimization
-- | - Color lookup tables
-- |
-- | Dimension is tracked at runtime.

module Hydrogen.Schema.Dimension.Vector.VecN
  ( VecN(VecN)
  , vecN
  , vecNZero
  , vecNFromArray
  , vecNToArray
  , dimVecN
  , addVecN
  , subtractVecN
  , scaleVecN
  , negateVecN
  , dotVecN
  , lengthSquaredVecN
  , lengthVecN
  , normalizeVecN
  , distanceVecN
  , lerpVecN
  , getComponentN
  , setComponentN
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Show
  , map
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Foldable (sum)
import Hydrogen.Math.Core as Math

-- | N-dimensional vector
newtype VecN a = VecN (Array a)

derive instance eqVecN :: Eq a => Eq (VecN a)

instance showVecN :: Show a => Show (VecN a) where
  show (VecN arr) = "VecN[" <> show (Array.length arr) <> "]"

instance functorVecN :: Functor VecN where
  map f (VecN arr) = VecN (map f arr)

-- | Create an N-dimensional vector from components
vecN :: forall a. Array a -> VecN a
vecN = VecN

-- | Create a zero vector of given dimension
vecNZero :: Int -> VecN Number
vecNZero dim = VecN (Array.replicate dim 0.0)

-- | Create from array
vecNFromArray :: forall a. Array a -> VecN a
vecNFromArray = VecN

-- | Convert to array
vecNToArray :: forall a. VecN a -> Array a
vecNToArray (VecN arr) = arr

-- | Get dimension of vector
dimVecN :: forall a. VecN a -> Int
dimVecN (VecN arr) = Array.length arr

-- | Add two N-dimensional vectors
addVecN :: VecN Number -> VecN Number -> VecN Number
addVecN (VecN a) (VecN b) = VecN (Array.zipWith (+) a b)

-- | Subtract two N-dimensional vectors
subtractVecN :: VecN Number -> VecN Number -> VecN Number
subtractVecN (VecN a) (VecN b) = VecN (Array.zipWith (-) a b)

-- | Scale an N-dimensional vector
scaleVecN :: Number -> VecN Number -> VecN Number
scaleVecN s (VecN arr) = VecN (map (_ * s) arr)

-- | Negate an N-dimensional vector
negateVecN :: VecN Number -> VecN Number
negateVecN (VecN arr) = VecN (map negate arr)

-- | Dot product of two N-dimensional vectors
dotVecN :: VecN Number -> VecN Number -> Number
dotVecN (VecN a) (VecN b) = sum (Array.zipWith (*) a b)

-- | Squared length of an N-dimensional vector
lengthSquaredVecN :: VecN Number -> Number
lengthSquaredVecN v = dotVecN v v

-- | Length of an N-dimensional vector
lengthVecN :: VecN Number -> Number
lengthVecN v = Math.sqrt (lengthSquaredVecN v)

-- | Normalize an N-dimensional vector
normalizeVecN :: VecN Number -> VecN Number
normalizeVecN v =
  let len = lengthVecN v
  in if len == 0.0 then v else scaleVecN (1.0 / len) v

-- | Distance between two N-dimensional points
distanceVecN :: VecN Number -> VecN Number -> Number
distanceVecN a b = lengthVecN (subtractVecN b a)

-- | Linear interpolation between two N-dimensional vectors
lerpVecN :: Number -> VecN Number -> VecN Number -> VecN Number
lerpVecN t (VecN a) (VecN b) = VecN (Array.zipWith (\x y -> Math.lerp x y t) a b)

-- | Get component at index (0-based)
getComponentN :: forall a. Int -> VecN a -> Maybe a
getComponentN idx (VecN arr) = Array.index arr idx

-- | Set component at index (0-based)
setComponentN :: forall a. Int -> a -> VecN a -> VecN a
setComponentN idx val (VecN arr) = 
  VecN (fromMaybe arr (Array.updateAt idx val arr))
