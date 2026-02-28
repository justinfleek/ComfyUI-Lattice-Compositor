-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // qrcode // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Exhaustive QRCode property tests.
-- |
-- | This is an orchestrating module that re-exports test suites from:
-- | - Test.QRCode.GaloisField
-- | - Test.QRCode.Polynomial
-- | - Test.QRCode.ReedSolomon
-- | - Test.QRCode.BitStream
-- | - Test.QRCode.Segment
-- | - Test.QRCode.Capacity
-- | - Test.QRCode.Matrix
-- | - Test.QRCode.Mask
-- | - Test.QRCode.Interleaving

module Test.QRCode (qrCodeTests) where

import Prelude
import Test.Spec (Spec)

import Test.QRCode.GaloisField (galoisFieldTests)
import Test.QRCode.Polynomial (polynomialTests)
import Test.QRCode.ReedSolomon (reedSolomonTests)
import Test.QRCode.BitStream (bitstreamTests)
import Test.QRCode.Segment (segmentEncodingTests)
import Test.QRCode.Capacity (capacityTableTests)
import Test.QRCode.Matrix (matrixStructureTests)
import Test.QRCode.Mask (maskingTests)
import Test.QRCode.Interleaving (interleavingTests)

qrCodeTests :: Spec Unit
qrCodeTests = do
  galoisFieldTests
  polynomialTests
  reedSolomonTests
  bitstreamTests
  segmentEncodingTests
  capacityTableTests
  matrixStructureTests
  maskingTests
  interleavingTests
