-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Offline storage — Pure Data
-- |
-- | Storage operations are modeled as **pure data commands**.
-- | The runtime interprets commands and produces results as messages.
-- |
-- | This is storage-backend agnostic: the runtime can implement using
-- | IndexedDB, SQLite, filesystem, distributed storage, etc.
-- |
-- | ## Pure Data Model
-- |
-- | ```purescript
-- | import Hydrogen.Offline.Storage as Storage
-- |
-- | -- Define a storage command
-- | fetchUser :: String -> Storage.StorageCommand User
-- | fetchUser userId = Storage.Get
-- |   { store: "users"
-- |   , key: userId
-- |   }
-- |
-- | -- Handle storage result in update
-- | update :: Msg -> Model -> Model
-- | update (GotUser result) model = case result of
-- |   Storage.Found user -> model { user = Just user }
-- |   Storage.NotFound -> model { error = Just "User not found" }
-- |   Storage.StorageError err -> model { error = Just err }
-- |
-- | -- Batch operations
-- | syncData :: Storage.StorageCommand (Array Post)
-- | syncData = Storage.GetAll { store: "posts" }
-- | ```
module Hydrogen.Offline.Storage
  ( -- * Storage Command (Pure Data)
    StorageCommand(..)
  , StoreName
  , StoreKey
    -- * Store Configuration (Pure Data)
  , StoreConfig
  , IndexConfig
  , defaultStoreConfig
  , storeWithKeyPath
  , storeWithAutoIncrement
    -- * Storage Result (Pure Data)
  , StorageResult(..)
  , StorageError(..)
    -- * Command Builders (Pure Functions)
  , put
  , get
  , getAll
  , getAllByIndex
  , delete
  , clear
  , count
  , keys
  , exists
    -- * Database Schema (Pure Data)
  , DatabaseSchema
  , SchemaStore
  , schema
  , addStore
  , addStoreWithIndexes
    -- * Transaction Mode (Pure Data)
  , TransactionMode(..)
  , Transaction
  , transaction
  , addCommand
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Store name — type alias for clarity
type StoreName = String

-- | Store key — type alias for clarity
type StoreKey = String

-- | Store configuration — pure data
type StoreConfig =
  { keyPath :: Maybe String
  , autoIncrement :: Boolean
  }

-- | Default store configuration
defaultStoreConfig :: StoreConfig
defaultStoreConfig =
  { keyPath: Nothing
  , autoIncrement: false
  }

-- | Create store config with key path
storeWithKeyPath :: String -> StoreConfig
storeWithKeyPath path =
  { keyPath: Just path
  , autoIncrement: false
  }

-- | Create store config with auto-increment
storeWithAutoIncrement :: StoreConfig
storeWithAutoIncrement =
  { keyPath: Nothing
  , autoIncrement: true
  }

-- | Index configuration — pure data
type IndexConfig =
  { name :: String
  , keyPath :: String
  , unique :: Boolean
  , multiEntry :: Boolean
  }

-- | Transaction mode — pure enum
data TransactionMode
  = ReadOnly
  | ReadWrite

derive instance eqTransactionMode :: Eq TransactionMode

instance showTransactionMode :: Show TransactionMode where
  show ReadOnly = "ReadOnly"
  show ReadWrite = "ReadWrite"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // storage commands
-- ═════════════════════════════════════════════════════════════════════════════

-- | Storage command — pure data describing a storage operation
-- |
-- | The runtime interprets these commands and produces StorageResult values.
-- | The `a` type parameter is the expected result type (phantom for type safety).
data StorageCommand a
  = Put
    { store :: StoreName
    , key :: Maybe StoreKey     -- Nothing = auto-generate
    , value :: a
    }
  | Get
    { store :: StoreName
    , key :: StoreKey
    }
  | GetAll
    { store :: StoreName
    }
  | GetAllByIndex
    { store :: StoreName
    , indexName :: String
    , indexValue :: String
    }
  | Delete
    { store :: StoreName
    , key :: StoreKey
    }
  | Clear
    { store :: StoreName
    }
  | Count
    { store :: StoreName
    }
  | Keys
    { store :: StoreName
    }
  | Exists
    { store :: StoreName
    , key :: StoreKey
    }

derive instance eqStorageCommand :: Eq a => Eq (StorageCommand a)

instance showStorageCommand :: Show a => Show (StorageCommand a) where
  show (Put r) = "Put { store: " <> r.store <> ", value: " <> show r.value <> " }"
  show (Get r) = "Get { store: " <> r.store <> ", key: " <> r.key <> " }"
  show (GetAll r) = "GetAll { store: " <> r.store <> " }"
  show (GetAllByIndex r) = "GetAllByIndex { store: " <> r.store <> ", index: " <> r.indexName <> " }"
  show (Delete r) = "Delete { store: " <> r.store <> ", key: " <> r.key <> " }"
  show (Clear r) = "Clear { store: " <> r.store <> " }"
  show (Count r) = "Count { store: " <> r.store <> " }"
  show (Keys r) = "Keys { store: " <> r.store <> " }"
  show (Exists r) = "Exists { store: " <> r.store <> ", key: " <> r.key <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // storage results
-- ═════════════════════════════════════════════════════════════════════════════

-- | Storage error — pure data
data StorageError
  = NotFound
  | StoreNotFound String
  | KeyError String
  | SerializationError String
  | QuotaExceeded
  | TransactionAborted
  | UnknownError String

derive instance eqStorageError :: Eq StorageError

instance showStorageError :: Show StorageError where
  show NotFound = "NotFound"
  show (StoreNotFound s) = "StoreNotFound: " <> s
  show (KeyError s) = "KeyError: " <> s
  show (SerializationError s) = "SerializationError: " <> s
  show QuotaExceeded = "QuotaExceeded"
  show TransactionAborted = "TransactionAborted"
  show (UnknownError s) = "UnknownError: " <> s

-- | Storage result — pure data representing operation outcome
data StorageResult a
  = Found a                     -- ^ Value found
  | Success                     -- ^ Operation succeeded (put, delete, clear)
  | CountResult Int             -- ^ Count result
  | KeysResult (Array StoreKey) -- ^ Keys result
  | ExistsResult Boolean        -- ^ Exists check result
  | AllFound (Array a)          -- ^ GetAll result
  | Error StorageError          -- ^ Operation failed

derive instance eqStorageResult :: Eq a => Eq (StorageResult a)

instance showStorageResult :: Show a => Show (StorageResult a) where
  show (Found a) = "Found " <> show a
  show Success = "Success"
  show (CountResult n) = "CountResult " <> show n
  show (KeysResult ks) = "KeysResult " <> show ks
  show (ExistsResult b) = "ExistsResult " <> show b
  show (AllFound as) = "AllFound " <> show as
  show (Error e) = "Error " <> show e

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // command builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a put command
put :: forall a. StoreName -> a -> StorageCommand a
put store value = Put { store, key: Nothing, value }

-- | Create a get command
get :: forall a. StoreName -> StoreKey -> StorageCommand a
get store key = Get { store, key }

-- | Create a get-all command
getAll :: forall a. StoreName -> StorageCommand a
getAll store = GetAll { store }

-- | Create a get-all-by-index command
getAllByIndex :: forall a. StoreName -> String -> String -> StorageCommand a
getAllByIndex store indexName indexValue = 
  GetAllByIndex { store, indexName, indexValue }

-- | Create a delete command
delete :: forall a. StoreName -> StoreKey -> StorageCommand a
delete store key = Delete { store, key }

-- | Create a clear command
clear :: forall a. StoreName -> StorageCommand a
clear store = Clear { store }

-- | Create a count command
count :: forall a. StoreName -> StorageCommand a
count store = Count { store }

-- | Create a keys command
keys :: forall a. StoreName -> StorageCommand a
keys store = Keys { store }

-- | Create an exists command
exists :: forall a. StoreName -> StoreKey -> StorageCommand a
exists store key = Exists { store, key }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // database schema
-- ═════════════════════════════════════════════════════════════════════════════

-- | Store definition in schema
type SchemaStore =
  { name :: StoreName
  , config :: StoreConfig
  , indexes :: Array IndexConfig
  }

-- | Database schema — pure data describing database structure
type DatabaseSchema =
  { name :: String
  , version :: Int
  , stores :: Array SchemaStore
  }

-- | Create empty database schema
schema :: String -> Int -> DatabaseSchema
schema name version =
  { name
  , version
  , stores: []
  }

-- | Add a store to schema
addStore :: StoreName -> StoreConfig -> DatabaseSchema -> DatabaseSchema
addStore name config db =
  db { stores = Array.snoc db.stores { name, config, indexes: [] } }

-- | Add a store with indexes to schema
addStoreWithIndexes :: StoreName -> StoreConfig -> Array IndexConfig -> DatabaseSchema -> DatabaseSchema
addStoreWithIndexes name config indexes db =
  db { stores = Array.snoc db.stores { name, config, indexes } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // transactions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transaction — pure data grouping multiple commands
type Transaction a =
  { stores :: Array StoreName
  , mode :: TransactionMode
  , commands :: Array (StorageCommand a)
  }

-- | Create a transaction
transaction :: forall a. Array StoreName -> TransactionMode -> Transaction a
transaction stores mode =
  { stores
  , mode
  , commands: []
  }

-- | Add a command to a transaction
addCommand :: forall a. StorageCommand a -> Transaction a -> Transaction a
addCommand cmd tx =
  tx { commands = Array.snoc tx.commands cmd }
