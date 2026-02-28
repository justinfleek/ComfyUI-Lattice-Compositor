-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // test // qrcode // interleaving
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Block interleaving tests.

module Test.QRCode.Interleaving (interleavingTests) where

import Prelude
import Test.Spec (Spec, describe, pending)

interleavingTests :: Spec Unit
interleavingTests = describe "Block Interleaving" do
  
  describe "Interleaving preserves data" do
    pending "total bytes preserved after interleaving - requires exposing interleave function"
    
    pending "all blocks contribute to final output - requires exposing interleave function"
