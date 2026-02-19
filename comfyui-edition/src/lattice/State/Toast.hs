-- |
-- Module      : Lattice.State.Toast
-- Description : Pure state management functions for toast store
-- 
-- Migrated from ui/src/stores/toastStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Toast
  ( -- Helper functions
    createToast
  -- Query functions
  , getToasts
  , findToastById
  , filterToastsByType
  -- Types
  , ToastType(..)
  , Toast(..)
  , ToastState(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  )
import Data.List (find, filter)
import Data.Maybe (Maybe)
import Data.Text (Text)
import GHC.Generics (Generic)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             // toast // type
-- ════════════════════════════════════════════════════════════════════════════

-- | Toast notification type
data ToastType
  = ToastTypeSuccess
  | ToastTypeError
  | ToastTypeWarning
  | ToastTypeInfo
  deriving (Eq, Show, Generic)

instance ToJSON ToastType where
  toJSON ToastTypeSuccess = "success"
  toJSON ToastTypeError = "error"
  toJSON ToastTypeWarning = "warning"
  toJSON ToastTypeInfo = "info"

instance FromJSON ToastType where
  parseJSON = withText "ToastType" $ \s ->
    case s of
      "success" -> return ToastTypeSuccess
      "error" -> return ToastTypeError
      "warning" -> return ToastTypeWarning
      "info" -> return ToastTypeInfo
      _ -> fail "Invalid ToastType"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // toast
-- ════════════════════════════════════════════════════════════════════════════

-- | Toast notification
data Toast = Toast
  { toastId :: Text
  , toastMessage :: Text
  , toastType :: ToastType
  , toastDuration :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON Toast where
  toJSON (Toast id_ message type_ duration) =
    object
      [ "id" .= id_
      , "message" .= message
      , "type" .= type_
      , "duration" .= duration
      ]

instance FromJSON Toast where
  parseJSON = withObject "Toast" $ \o -> do
    id_ <- o .: "id"
    message <- o .: "message"
    type_ <- o .: "type"
    duration <- o .: "duration"
    return (Toast id_ message type_ duration)

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // toast // state
-- ════════════════════════════════════════════════════════════════════════════

-- | Toast store state
data ToastState = ToastState
  { toastStateToasts :: [Toast]
  }
  deriving (Eq, Show, Generic)

instance ToJSON ToastState where
  toJSON (ToastState toasts) =
    object ["toasts" .= toasts]

instance FromJSON ToastState where
  parseJSON = withObject "ToastState" $ \o -> do
    toasts <- o .: "toasts"
    return (ToastState toasts)

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a toast notification
-- Pure function: takes id, message, type, duration, returns Toast
createToast :: Text -> Text -> ToastType -> Double -> Toast
createToast id_ message type_ duration =
  Toast
    { toastId = id_
    , toastMessage = message
    , toastType = type_
    , toastDuration = duration
    }

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get all toasts
-- Pure function: takes toast list, returns toast list
getToasts :: [Toast] -> [Toast]
getToasts toasts = toasts

-- | Find toast by ID
-- Pure function: takes toast ID and toast list, returns toast or Nothing
findToastById :: Text -> [Toast] -> Maybe Toast
findToastById id_ toasts = find (\t -> toastId t == id_) toasts

-- | Filter toasts by type
-- Pure function: takes toast type and toast list, returns filtered list
filterToastsByType :: ToastType -> [Toast] -> [Toast]
filterToastsByType type_ toasts = filter (\t -> toastType t == type_) toasts
