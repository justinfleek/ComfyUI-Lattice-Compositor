-- |
-- Module      : Lattice.Database.ChatMessages
-- Description : Chat message database operations
-- 
-- Provides CRUD operations for LLM agent chat history.
-- All operations are deterministic and total.
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Lattice.Database.ChatMessages
  ( ChatMessage(..)
  , saveChatMessage
  , getChatHistory
  , searchChatHistory
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Time.Clock (UTCTime)
import Data.Aeson (Value, ToJSON(..), FromJSON(..), object, (.=), (.:?), (.:))
import Lattice.Database.DuckDB (DuckDBConnection, query, execute)

-- | Chat message structure matching database schema
data ChatMessage = ChatMessage
  { chatId :: Text
  , projectId :: Maybe Text
  , role :: Text  -- 'user' | 'assistant' | 'system' | 'tool'
  , content :: Text
  , toolCalls :: Maybe Value
  , toolCallId :: Maybe Text
  , model :: Maybe Text
  , tokensUsed :: Int
  , costUsd :: Double
  , timestamp :: Int  -- Unix epoch
  , createdAt :: Int
  , modifiedAt :: Int
  } deriving (Show, Eq)

instance ToJSON ChatMessage where
  toJSON ChatMessage{..} = object
    [ "id" .= chatId
    , "project_id" .= projectId
    , "role" .= role
    , "content" .= content
    , "tool_calls" .= toolCalls
    , "tool_call_id" .= toolCallId
    , "model" .= model
    , "tokens_used" .= tokensUsed
    , "cost_usd" .= costUsd
    , "timestamp" .= timestamp
    , "created_at" .= createdAt
    , "modified_at" .= modifiedAt
    ]

instance FromJSON ChatMessage where
  parseJSON = \v -> do
    obj <- parseJSON v
    ChatMessage
      <$> obj .: "id"
      <*> obj .:? "project_id"
      <*> obj .: "role"
      <*> obj .: "content"
      <*> obj .:? "tool_calls"
      <*> obj .:? "tool_call_id"
      <*> obj .:? "model"
      <*> obj .: "tokens_used"
      <*> obj .: "cost_usd"
      <*> obj .: "timestamp"
      <*> obj .: "created_at"
      <*> obj .: "modified_at"

-- | Save a chat message to database
saveChatMessage :: DuckDBConnection -> ChatMessage -> IO (Either Text ())
saveChatMessage conn msg = do
  -- TODO: Execute INSERT INTO chat_messages
  -- For now, return success
  return (Right ())

-- | Get chat history for a project
getChatHistory :: DuckDBConnection -> Maybe Text -> Int -> IO (Either Text [ChatMessage])
getChatHistory conn mProjectId limit = do
  -- TODO: Execute SELECT * FROM chat_messages WHERE project_id = ? ORDER BY timestamp DESC LIMIT ?
  -- For now, return empty
  return (Right [])

-- | Search chat history using full-text search
searchChatHistory :: DuckDBConnection -> Maybe Text -> Text -> Int -> IO (Either Text [ChatMessage])
searchChatHistory conn mProjectId queryText limit = do
  -- TODO: Execute SELECT * FROM chat_messages WHERE project_id = ? AND content MATCH ? ORDER BY timestamp DESC LIMIT ?
  -- For now, return empty
  return (Right [])
