-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // worldmodel // pan
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PAN World Model - Generative Latent Prediction (GLP) Architecture
-- |
-- | Reference: arXiv 2511.09057 (MBZUAI, 2025)
-- |
-- | ## Architecture
-- |
-- | ```
-- | Encoder h: o_t → ŝ_t              (Observation → Latent)
-- | Predictor f: (ŝ_t, a_t) → ŝ_{t+1} (Dynamics)
-- | Decoder g: ŝ_{t+1} → ô_{t+1}      (Latent → Observation)
-- | ```

module Hydrogen.WorldModel.PAN
  ( -- * GLP Components
    Encoder(..)
  , Predictor(..)
  , Decoder(..)
  
  -- * PAN Model
  , PANModel(..)
  , createPAN
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude (class Eq, class Show)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // glp // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encoder: Maps observation to latent representation.
-- | ŝ_t ~ p_h(· | o_t)
data Encoder = Encoder

derive instance eqEncoder :: Eq Encoder
instance showEncoder :: Show Encoder where
  show Encoder = "Encoder"

-- | Predictor: Models latent world dynamics.
-- | ŝ_{t+1} ~ p_f(· | ŝ_t, a_t)
data Predictor = Predictor

derive instance eqPredictor :: Eq Predictor
instance showPredictor :: Show Predictor where
  show Predictor = "Predictor"

-- | Decoder: Reconstructs observation from latent.
-- | ô_{t+1} ~ p_g(· | ŝ_{t+1})
data Decoder = Decoder

derive instance eqDecoder :: Eq Decoder
instance showDecoder :: Show Decoder where
  show Decoder = "Decoder"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // pan // model
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete PAN world model.
data PANModel = PANModel
  { encoder :: Encoder
  , predictor :: Predictor
  , decoder :: Decoder
  }

derive instance eqPANModel :: Eq PANModel
instance showPANModel :: Show PANModel where
  show (PANModel _) = "PANModel"

-- | Create a PAN model with default components.
createPAN :: PANModel
createPAN = PANModel
  { encoder: Encoder
  , predictor: Predictor
  , decoder: Decoder
  }
