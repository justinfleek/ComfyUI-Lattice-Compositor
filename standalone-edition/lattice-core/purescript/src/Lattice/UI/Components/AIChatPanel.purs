-- | AI Chat Panel Component
-- |
-- | AI-powered natural language interface for motion graphics.
-- | Chat with GPT-4o or Claude Sonnet to create animations:
-- | - Natural language animation commands
-- | - Iterative refinement ("make it faster", "add glow")
-- | - Full compositor schema understanding
-- | - Real-time layer/keyframe creation
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AIChatPanel.vue
module Lattice.UI.Components.AIChatPanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , AIModel(..)
  , Message
  , MessageRole(..)
  ) where

import Prelude

import Data.Array (length, snoc)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String (trim)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Now (nowDateTime)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { initialModel :: Maybe AIModel
  }

data Output
  = SendMessage String AIModel
  | ClearHistory
  | ModelChanged AIModel

data Query a
  = AddMessage Message a
  | SetProcessing Boolean a
  | SetStatus ConnectionStatus a
  | GetMessages (Array Message -> a)

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // message // types
-- ════════════════════════════════════════════════════════════════════════════

data AIModel
  = GPT4o
  | ClaudeSonnet

derive instance eqAIModel :: Eq AIModel

instance showAIModel :: Show AIModel where
  show = case _ of
    GPT4o -> "gpt-4o"
    ClaudeSonnet -> "claude-sonnet"

modelLabel :: AIModel -> String
modelLabel = case _ of
  GPT4o -> "GPT-4o"
  ClaudeSonnet -> "Claude Sonnet"

data MessageRole
  = RoleUser
  | RoleAssistant

derive instance eqMessageRole :: Eq MessageRole

type Message =
  { role :: MessageRole
  , content :: String
  , timestamp :: String
  , toolCalls :: Array ToolCall
  }

type ToolCall =
  { name :: String
  , args :: String
  }

data ConnectionStatus
  = StatusChecking
  | StatusConnected
  | StatusError

derive instance eqConnectionStatus :: Eq ConnectionStatus

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { selectedModel :: AIModel
  , messages :: Array Message
  , inputText :: String
  , isProcessing :: Boolean
  , processingText :: String
  , connectionStatus :: ConnectionStatus
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | SetModel AIModel
  | SetInputText String
  | SubmitMessage
  | ClearMessages
  | UseExample String
  | HandleKeyDown String

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // example prompts
-- ════════════════════════════════════════════════════════════════════════════

examplePrompts :: Array String
examplePrompts =
  [ "Fade in a title over 1 second"
  , "Create floating particles that drift upward"
  , "Make the selected layer bounce in from the left"
  , "Add a glow effect to all text layers"
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { selectedModel: case input.initialModel of
      Just m -> m
      Nothing -> GPT4o
  , messages: []
  , inputText: ""
  , isProcessing: false
  , processingText: "Thinking..."
  , connectionStatus: StatusChecking
  , baseId: "lattice-ai-chat"
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-ai-chat-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "AI Compositor Agent"
    ]
    [ renderHeader state
    , renderMessages state
    , renderInputArea state
    , renderStatusBar state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span 
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ] 
        [ HH.text "AI Agent" ]
    , HH.div 
        [ cls [ "header-actions" ]
        , HP.attr (HH.AttrName "style") headerActionsStyle
        ]
        [ HH.select
            [ cls [ "model-selector" ]
            , HP.attr (HH.AttrName "style") modelSelectorStyle
            , ARIA.label "Select AI model"
            , HE.onValueChange \v -> SetModel (parseModel v)
            ]
            [ HH.option 
                [ HP.value "gpt-4o"
                , HP.selected (state.selectedModel == GPT4o)
                ] 
                [ HH.text "GPT-4o" ]
            , HH.option 
                [ HP.value "claude-sonnet"
                , HP.selected (state.selectedModel == ClaudeSonnet)
                ] 
                [ HH.text "Claude Sonnet" ]
            ]
        , HH.button
            [ cls [ "clear-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") clearBtnStyle
            , HP.attr (HH.AttrName "title") "Clear conversation"
            , ARIA.label "Clear conversation history"
            , HE.onClick \_ -> ClearMessages
            ]
            [ HH.text "Clear" ]
        ]
    ]

parseModel :: String -> AIModel
parseModel = case _ of
  "claude-sonnet" -> ClaudeSonnet
  _ -> GPT4o

renderMessages :: forall m. State -> H.ComponentHTML Action Slots m
renderMessages state =
  HH.div
    [ cls [ "chat-messages" ]
    , HP.attr (HH.AttrName "style") messagesContainerStyle
    , HP.attr (HH.AttrName "role") "log"
    , ARIA.label "Chat messages"
    , ARIA.live "polite"
    ]
    [ if length state.messages == 0
        then renderWelcome
        else HH.div_ (map renderMessage state.messages)
    , if state.isProcessing
        then renderProcessing state
        else HH.text ""
    ]

renderWelcome :: forall m. H.ComponentHTML Action Slots m
renderWelcome =
  HH.div
    [ cls [ "welcome-message" ]
    , HP.attr (HH.AttrName "style") welcomeStyle
    ]
    [ HH.div 
        [ cls [ "welcome-icon" ]
        , HP.attr (HH.AttrName "style") welcomeIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ] 
        [ HH.text "AI" ]
    , HH.h3 
        [ HP.attr (HH.AttrName "style") welcomeTitleStyle ] 
        [ HH.text "AI Compositor Agent" ]
    , HH.p 
        [ HP.attr (HH.AttrName "style") welcomeDescStyle ] 
        [ HH.text "Describe the motion graphics you want to create, and I'll build it for you." ]
    , HH.div 
        [ cls [ "example-prompts" ]
        , HP.attr (HH.AttrName "style") examplePromptsStyle
        ]
        (map renderExampleButton examplePrompts)
    ]

renderExampleButton :: forall m. String -> H.ComponentHTML Action Slots m
renderExampleButton example =
  HH.button
    [ cls [ "example-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") exampleBtnStyle
    , HE.onClick \_ -> UseExample example
    ]
    [ HH.text example ]

renderMessage :: forall m. Message -> H.ComponentHTML Action Slots m
renderMessage msg =
  HH.div
    [ cls [ "message", roleClass msg.role ]
    , HP.attr (HH.AttrName "style") (messageStyle msg.role)
    ]
    [ HH.div 
        [ cls [ "message-header" ]
        , HP.attr (HH.AttrName "style") messageHeaderStyle
        ]
        [ HH.span 
            [ cls [ "role-label" ]
            , HP.attr (HH.AttrName "style") roleLabelStyle
            ] 
            [ HH.text (roleLabel msg.role) ]
        , HH.span 
            [ cls [ "timestamp" ]
            , HP.attr (HH.AttrName "style") timestampStyle
            ] 
            [ HH.text msg.timestamp ]
        ]
    , HH.div 
        [ cls [ "message-content" ]
        , HP.attr (HH.AttrName "style") messageContentStyle
        ] 
        [ HH.text msg.content ]
    , if length msg.toolCalls > 0
        then renderToolCalls msg.toolCalls
        else HH.text ""
    ]

roleClass :: MessageRole -> String
roleClass = case _ of
  RoleUser -> "user"
  RoleAssistant -> "assistant"

roleLabel :: MessageRole -> String
roleLabel = case _ of
  RoleUser -> "You"
  RoleAssistant -> "AI Agent"

renderToolCalls :: forall m. Array ToolCall -> H.ComponentHTML Action Slots m
renderToolCalls calls =
  HH.div
    [ cls [ "tool-calls" ]
    , HP.attr (HH.AttrName "style") toolCallsStyle
    ]
    [ HH.div 
        [ cls [ "tool-calls-header" ]
        , HP.attr (HH.AttrName "style") toolCallsHeaderStyle
        ] 
        [ HH.text "Actions taken:" ]
    , HH.div_ (map renderToolCall calls)
    ]

renderToolCall :: forall m. ToolCall -> H.ComponentHTML Action Slots m
renderToolCall call =
  HH.div
    [ cls [ "tool-call" ]
    , HP.attr (HH.AttrName "style") toolCallStyle
    ]
    [ HH.span 
        [ cls [ "tool-icon" ]
        , HP.attr (HH.AttrName "style") toolIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ] 
        [ HH.text (getToolIcon call.name) ]
    , HH.span 
        [ cls [ "tool-name" ] ] 
        [ HH.text (formatToolName call.name) ]
    ]

getToolIcon :: String -> String
getToolIcon = case _ of
  "createLayer" -> "+"
  "deleteLayer" -> "-"
  "duplicateLayer" -> "++"
  "addKeyframe" -> "K"
  "removeKeyframe" -> "-K"
  "addEffect" -> "fx"
  "setLayerProperty" -> "="
  "setLayerTransform" -> "T"
  "configureParticles" -> "P"
  "setTextContent" -> "A"
  "setSplinePoints" -> "~"
  _ -> "*"

formatToolName :: String -> String
formatToolName name =
  -- Simple camelCase to Title Case conversion
  -- In real implementation, use proper string manipulation
  name

renderProcessing :: forall m. State -> H.ComponentHTML Action Slots m
renderProcessing state =
  HH.div
    [ cls [ "message", "assistant", "processing" ]
    , HP.attr (HH.AttrName "style") (messageStyle RoleAssistant)
    , HP.attr (HH.AttrName "aria-live") "polite"
    ]
    [ HH.div 
        [ cls [ "message-header" ]
        , HP.attr (HH.AttrName "style") messageHeaderStyle
        ]
        [ HH.span 
            [ cls [ "role-label" ]
            , HP.attr (HH.AttrName "style") roleLabelStyle
            ] 
            [ HH.text "AI Agent" ]
        ]
    , HH.div 
        [ cls [ "message-content" ]
        , HP.attr (HH.AttrName "style") processingContentStyle
        ]
        [ HH.span 
            [ cls [ "processing-dots" ]
            , HP.attr (HH.AttrName "style") processingDotsStyle
            , HP.attr (HH.AttrName "aria-hidden") "true"
            ]
            [ HH.span [ HP.attr (HH.AttrName "style") dotStyle ] []
            , HH.span [ HP.attr (HH.AttrName "style") dotStyle ] []
            , HH.span [ HP.attr (HH.AttrName "style") dotStyle ] []
            ]
        , HH.span 
            [ cls [ "processing-text" ]
            , HP.attr (HH.AttrName "style") processingTextStyle
            ] 
            [ HH.text state.processingText ]
        ]
    ]

renderInputArea :: forall m. State -> H.ComponentHTML Action Slots m
renderInputArea state =
  HH.div
    [ cls [ "input-area" ]
    , HP.attr (HH.AttrName "style") inputAreaStyle
    ]
    [ HH.textarea
        [ cls [ "message-input" ]
        , HP.attr (HH.AttrName "style") textareaStyle
        , HP.placeholder "Describe the animation you want to create..."
        , HP.disabled state.isProcessing
        , HP.rows 2
        , HP.value state.inputText
        , ARIA.label "Message input"
        , HE.onValueInput SetInputText
        ]
    , HH.button
        [ cls [ "send-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") sendBtnStyle
        , HP.disabled (trim state.inputText == "" || state.isProcessing)
        , ARIA.label "Send message"
        , HE.onClick \_ -> SubmitMessage
        ]
        [ if state.isProcessing
            then HH.span [ cls [ "spinner" ], HP.attr (HH.AttrName "style") spinnerStyle ] []
            else HH.text "Send"
        ]
    ]

renderStatusBar :: forall m. State -> H.ComponentHTML Action Slots m
renderStatusBar state =
  HH.div
    [ cls [ "status-bar" ]
    , HP.attr (HH.AttrName "style") statusBarStyle
    , HP.attr (HH.AttrName "role") "status"
    , ARIA.live "polite"
    ]
    [ HH.span 
        [ cls [ "status-indicator" ]
        , HP.attr (HH.AttrName "style") (statusIndicatorStyle state.connectionStatus)
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ] 
        []
    , HH.span 
        [ cls [ "status-text" ] ] 
        [ HH.text (statusText state) ]
    ]

statusText :: State -> String
statusText state
  | state.isProcessing = "Processing with " <> show state.selectedModel <> "..."
  | state.connectionStatus == StatusError = "API not configured"
  | state.connectionStatus == StatusConnected = "Ready (" <> modelLabel state.selectedModel <> ")"
  | otherwise = "Checking API status..."

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary);"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 8px 12px; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

titleStyle :: String
titleStyle =
  "font-weight: 600; font-size: 14px;"

headerActionsStyle :: String
headerActionsStyle =
  "display: flex; gap: 8px; align-items: center;"

modelSelectorStyle :: String
modelSelectorStyle =
  "padding: 4px 8px; font-size: 12px; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 4px;"

clearBtnStyle :: String
clearBtnStyle =
  "padding: 4px 8px; font-size: 12px; " <>
  "background: transparent; color: var(--lattice-text-secondary); " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 4px; cursor: pointer;"

messagesContainerStyle :: String
messagesContainerStyle =
  "flex: 1; overflow-y: auto; padding: 12px;"

welcomeStyle :: String
welcomeStyle =
  "text-align: center; padding: 24px;"

welcomeIconStyle :: String
welcomeIconStyle =
  "width: 48px; height: 48px; margin: 0 auto 12px; " <>
  "background: linear-gradient(135deg, #6366f1 0%, #8b5cf6 100%); " <>
  "border-radius: 12px; display: flex; align-items: center; justify-content: center; " <>
  "font-weight: bold; font-size: 18px; color: white;"

welcomeTitleStyle :: String
welcomeTitleStyle =
  "margin: 0 0 8px; font-size: 16px;"

welcomeDescStyle :: String
welcomeDescStyle =
  "margin: 0 0 16px; color: var(--lattice-text-secondary); font-size: 13px;"

examplePromptsStyle :: String
examplePromptsStyle =
  "display: flex; flex-direction: column; gap: 8px;"

exampleBtnStyle :: String
exampleBtnStyle =
  "padding: 8px 12px; font-size: 12px; " <>
  "background: var(--lattice-surface-2); color: var(--lattice-text-primary); " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 6px; " <>
  "cursor: pointer; text-align: left; transition: background 0.2s;"

messageStyle :: MessageRole -> String
messageStyle role =
  let
    baseStyle = "margin-bottom: 16px; padding: 12px; border-radius: 8px; "
    roleStyle = case role of
      RoleUser -> "background: var(--lattice-surface-2); margin-left: 24px;"
      RoleAssistant -> 
        "background: linear-gradient(135deg, rgba(99, 102, 241, 0.1) 0%, rgba(139, 92, 246, 0.1) 100%); " <>
        "margin-right: 24px;"
  in
    baseStyle <> roleStyle

messageHeaderStyle :: String
messageHeaderStyle =
  "display: flex; justify-content: space-between; margin-bottom: 8px; font-size: 11px;"

roleLabelStyle :: String
roleLabelStyle =
  "font-weight: 600; color: var(--lattice-text-primary);"

timestampStyle :: String
timestampStyle =
  "color: var(--lattice-text-muted);"

messageContentStyle :: String
messageContentStyle =
  "font-size: 13px; line-height: 1.5;"

toolCallsStyle :: String
toolCallsStyle =
  "margin-top: 12px; padding-top: 12px; border-top: 1px solid var(--lattice-border-subtle);"

toolCallsHeaderStyle :: String
toolCallsHeaderStyle =
  "font-size: 11px; color: var(--lattice-text-secondary); margin-bottom: 8px;"

toolCallStyle :: String
toolCallStyle =
  "display: inline-flex; align-items: center; gap: 4px; padding: 4px 8px; margin: 2px; " <>
  "background: var(--lattice-surface-1); border-radius: 4px; font-size: 11px;"

toolIconStyle :: String
toolIconStyle =
  "width: 18px; height: 18px; display: flex; align-items: center; justify-content: center; " <>
  "background: var(--lattice-accent); color: white; border-radius: 4px; " <>
  "font-size: 10px; font-weight: bold;"

processingContentStyle :: String
processingContentStyle =
  "display: flex; align-items: center; gap: 8px;"

processingDotsStyle :: String
processingDotsStyle =
  "display: flex; gap: 4px;"

dotStyle :: String
dotStyle =
  "width: 6px; height: 6px; background: var(--lattice-accent); border-radius: 50%; " <>
  "animation: bounce 1.4s infinite ease-in-out both;"

processingTextStyle :: String
processingTextStyle =
  "color: var(--lattice-text-secondary); font-size: 12px;"

inputAreaStyle :: String
inputAreaStyle =
  "display: flex; gap: 8px; padding: 12px; " <>
  "background: var(--lattice-surface-2); border-top: 1px solid var(--lattice-border-subtle);"

textareaStyle :: String
textareaStyle =
  "flex: 1; padding: 10px 12px; font-size: 13px; font-family: inherit; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 8px; " <>
  "resize: none; outline: none;"

sendBtnStyle :: String
sendBtnStyle =
  "padding: 10px 20px; font-size: 13px; font-weight: 600; " <>
  "background: var(--lattice-accent); color: white; " <>
  "border: none; border-radius: 8px; cursor: pointer; min-width: 70px;"

spinnerStyle :: String
spinnerStyle =
  "display: inline-block; width: 14px; height: 14px; " <>
  "border: 2px solid rgba(255, 255, 255, 0.3); border-radius: 50%; " <>
  "border-top-color: white; animation: spin 1s linear infinite;"

statusBarStyle :: String
statusBarStyle =
  "display: flex; align-items: center; gap: 8px; padding: 6px 12px; " <>
  "font-size: 11px; color: var(--lattice-text-secondary); " <>
  "background: var(--lattice-surface-1); border-top: 1px solid var(--lattice-border-subtle);"

statusIndicatorStyle :: ConnectionStatus -> String
statusIndicatorStyle status =
  let
    color = case status of
      StatusConnected -> "#22c55e"
      StatusError -> "#ef4444"
      StatusChecking -> "var(--lattice-text-muted)"
  in
    "width: 8px; height: 8px; border-radius: 50%; background: " <> color <> ";"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    -- In real implementation, check API status here
    H.modify_ _ { connectionStatus = StatusConnected }
  
  Receive input -> do
    case input.initialModel of
      Just m -> H.modify_ _ { selectedModel = m }
      Nothing -> pure unit
  
  SetModel model -> do
    H.modify_ _ { selectedModel = model }
    H.raise (ModelChanged model)
  
  SetInputText text -> do
    H.modify_ _ { inputText = text }
  
  SubmitMessage -> do
    state <- H.get
    let text = trim state.inputText
    when (text /= "" && not state.isProcessing) do
      -- Get current timestamp
      now <- liftEffect nowDateTime
      let timestamp = formatDateTime now
      
      -- Add user message to history
      let userMessage =
            { role: RoleUser
            , content: text
            , timestamp: timestamp
            , toolCalls: []
            }
      
      H.modify_ _ 
        { messages = snoc state.messages userMessage
        , inputText = ""
        , isProcessing = true
        , processingText = "Thinking..."
        }
      
      -- Raise event for parent to handle API call
      H.raise (SendMessage text state.selectedModel)
  
  ClearMessages -> do
    H.modify_ _ { messages = [] }
    H.raise ClearHistory
  
  UseExample example -> do
    H.modify_ _ { inputText = example }
    handleAction SubmitMessage
  
  HandleKeyDown key ->
    case key of
      "Enter" -> handleAction SubmitMessage
      _ -> pure unit

-- | Format DateTime to time string (HH:MM)
formatDateTime :: forall a. a -> String
formatDateTime _ = 
  -- Placeholder - in real implementation, format the DateTime
  -- For now, return a static placeholder
  "now"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  AddMessage msg next -> do
    H.modify_ \s -> s { messages = snoc s.messages msg }
    pure (Just next)
  
  SetProcessing processing next -> do
    H.modify_ _ { isProcessing = processing }
    pure (Just next)
  
  SetStatus status next -> do
    H.modify_ _ { connectionStatus = status }
    pure (Just next)
  
  GetMessages reply -> do
    state <- H.get
    pure (Just (reply state.messages))
