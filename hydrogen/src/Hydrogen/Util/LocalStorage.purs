-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // local-storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Type-safe localStorage utilities
-- |
-- | Provides type-safe access to localStorage with JSON encoding/decoding.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.LocalStorage as LS
-- |
-- | -- Store a value (any type with EncodeJson)
-- | LS.setItem "user" { name: "Alice", age: 30 }
-- |
-- | -- Retrieve a value (any type with DecodeJson)
-- | maybeUser :: Maybe User <- LS.getItem "user"
-- |
-- | -- Remove a value
-- | LS.removeItem "user"
-- |
-- | -- Clear all storage
-- | LS.clear
-- |
-- | -- Listen for changes
-- | unsubscribe <- LS.onChange "user" \maybeValue ->
-- |   Console.log $ "User changed: " <> show maybeValue
-- |
-- | -- With namespacing
-- | ns <- LS.namespace "myapp"
-- | ns.setItem "setting" true
-- | ns.getItem "setting"  -- Stored as "myapp:setting"
-- | ```
module Hydrogen.Util.LocalStorage
  ( -- * Core Operations
    getItem
  , setItem
  , removeItem
  , clear
    -- * String Operations (no encoding)
  , getItemRaw
  , setItemRaw
    -- * Change Listening
  , onChange
  , onAnyChange
    -- * Namespacing
  , namespace
  , Namespaced
  , getItemPrefixed
  , setItemPrefixed
    -- * Utilities
  , keys
  , length
  , has
  ) where

import Prelude hiding (void)

import Data.Argonaut (class DecodeJson, class EncodeJson, decodeJson, encodeJson, parseJson, stringify)
import Data.Either (hush)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Effect (Effect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespaced storage interface
-- | Note: For type-safe operations, use the prefixed versions of getItem/setItem
type Namespaced =
  { getItemRaw :: String -> Effect (Maybe String)
  , setItemRaw :: String -> String -> Effect Unit
  , removeItem :: String -> Effect Unit
  , clear :: Effect Unit
  , keys :: Effect (Array String)
  , prefix :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

foreign import getItemImpl :: String -> Effect (Maybe String)

foreign import setItemImpl :: String -> String -> Effect Unit

foreign import removeItemImpl :: String -> Effect Unit

foreign import clearImpl :: Effect Unit

foreign import keysImpl :: Effect (Array String)

foreign import lengthImpl :: Effect Int

foreign import onChangeImpl 
  :: String 
  -> (Maybe String -> Effect Unit) 
  -> Effect (Effect Unit)

foreign import onAnyChangeImpl 
  :: (String -> Maybe String -> Effect Unit) 
  -> Effect (Effect Unit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // core operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get an item from localStorage with JSON decoding
-- |
-- | Returns `Nothing` if the key doesn't exist or decoding fails.
-- |
-- | ```purescript
-- | maybeUser :: Maybe User <- getItem "user"
-- | ```
getItem :: forall a. DecodeJson a => String -> Effect (Maybe a)
getItem key = do
  maybeStr <- getItemImpl key
  pure $ case maybeStr of
    Nothing -> Nothing
    Just str -> hush (parseJson str) >>= hush <<< decodeJson

-- | Set an item in localStorage with JSON encoding
-- |
-- | ```purescript
-- | setItem "settings" { theme: "dark", fontSize: 14 }
-- | ```
setItem :: forall a. EncodeJson a => String -> a -> Effect Unit
setItem key value = setItemImpl key (stringify $ encodeJson value)

-- | Remove an item from localStorage
removeItem :: String -> Effect Unit
removeItem = removeItemImpl

-- | Clear all items from localStorage
clear :: Effect Unit
clear = clearImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // string operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a raw string from localStorage (no JSON decoding)
getItemRaw :: String -> Effect (Maybe String)
getItemRaw = getItemImpl

-- | Set a raw string in localStorage (no JSON encoding)
setItemRaw :: String -> String -> Effect Unit
setItemRaw = setItemImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // change listening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Listen for changes to a specific key
-- |
-- | Fires when the key is changed from another tab/window.
-- | Note: Does not fire for changes in the same tab.
-- |
-- | ```purescript
-- | unsubscribe <- onChange "user" \maybeValue ->
-- |   case maybeValue of
-- |     Nothing -> Console.log "User removed"
-- |     Just value -> Console.log $ "User updated: " <> value
-- | ```
onChange :: String -> (Maybe String -> Effect Unit) -> Effect (Effect Unit)
onChange = onChangeImpl

-- | Listen for any storage changes
-- |
-- | Callback receives the key and new value.
onAnyChange :: (String -> Maybe String -> Effect Unit) -> Effect (Effect Unit)
onAnyChange = onAnyChangeImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // namespacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a namespaced storage interface
-- |
-- | All keys are prefixed with the namespace.
-- |
-- | ```purescript
-- | ns <- namespace "myapp"
-- | ns.setItemRaw "theme" "dark"  -- Stored as "myapp:theme"
-- | maybeTheme <- ns.getItemRaw "theme"
-- | ns.clear  -- Only clears "myapp:*" keys
-- |
-- | -- For typed access, use the prefix:
-- | setItem (ns.prefix <> ":setting") myValue
-- | ```
namespace :: String -> Effect Namespaced
namespace prefix = pure
  { getItemRaw: \key -> getItemRaw (prefix <> ":" <> key)
  , setItemRaw: \key value -> setItemRaw (prefix <> ":" <> key) value
  , removeItem: \key -> removeItem (prefix <> ":" <> key)
  , clear: clearNamespace prefix
  , keys: getNamespaceKeys prefix
  , prefix
  }

-- | Clear all keys with a given prefix
clearNamespace :: String -> Effect Unit
clearNamespace prefix = do
  allKeys <- keysImpl
  let prefixedKeys = filterPrefix (prefix <> ":") allKeys
  traverse_ removeItem prefixedKeys
  where
  filterPrefix p arr = filter (startsWith p) arr
  
  startsWith :: String -> String -> Boolean
  startsWith p str = take (strLength p) str == p
  
  filter :: forall a. (a -> Boolean) -> Array a -> Array a
  filter = filterImpl
  
  traverse_ :: forall a. (a -> Effect Unit) -> Array a -> Effect Unit
  traverse_ f arr = void $ traverseImpl f arr

foreign import filterImpl :: forall a. (a -> Boolean) -> Array a -> Array a
foreign import traverseImpl :: forall a b. (a -> Effect b) -> Array a -> Effect (Array b)
foreign import take :: Int -> String -> String
foreign import strLength :: String -> Int

-- | Get all keys with a given prefix
getNamespaceKeys :: String -> Effect (Array String)
getNamespaceKeys prefix = do
  allKeys <- keysImpl
  pure $ filterImpl (startsWith (prefix <> ":")) allKeys
  where
  startsWith :: String -> String -> Boolean
  startsWith p str = take (strLength p) str == p

-- | Get a prefixed item with type safety
getItemPrefixed :: forall a. DecodeJson a => String -> String -> Effect (Maybe a)
getItemPrefixed prefix key = getItem (prefix <> ":" <> key)

-- | Set a prefixed item with type safety
setItemPrefixed :: forall a. EncodeJson a => String -> String -> a -> Effect Unit
setItemPrefixed prefix key value = setItem (prefix <> ":" <> key) value

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all keys in localStorage
keys :: Effect (Array String)
keys = keysImpl

-- | Get the number of items in localStorage
length :: Effect Int
length = lengthImpl

-- | Check if a key exists in localStorage
has :: String -> Effect Boolean
has key = isJust <$> getItemImpl key

-- Local void helper
void :: forall a. Effect a -> Effect Unit
void action = do
  _ <- action
  pure unit
