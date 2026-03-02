-- |
-- Module      : Lattice.FFI.LayerDefaultsState
-- Description : FFI bindings for layer defaults state management
-- 
-- Foreign function interface for Lattice.State.LayerDefaults
-- Provides C-compatible functions for Python/TypeScript interop
--

{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.LayerDefaultsState where

import Data.Aeson (encode, object, (.=), ToJSON(..))
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Foreign.C.String (CString, newCString)
import Lattice.State.LayerDefaults
  ( createDefaultTPoseKeypoints
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // json // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create success response JSON
successResponse :: ToJSON a => a -> BSL.ByteString
successResponse result = encode $ object ["status" .= ("success" :: T.Text), "result" .= result]

-- | Convert ByteString to CString
jsonToCString :: BSL.ByteString -> IO CString
jsonToCString = newCString . T.unpack . TE.decodeUtf8 . BSL.toStrict

-- ════════════════════════════════════════════════════════════════════════════
--                                         // keypoint // creation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | FFI: Create default T-pose keypoints
foreign export ccall create_default_t_pose_keypoints_ffi :: IO CString
create_default_t_pose_keypoints_ffi :: IO CString
create_default_t_pose_keypoints_ffi = do
  let result = createDefaultTPoseKeypoints
  jsonToCString (successResponse result)
