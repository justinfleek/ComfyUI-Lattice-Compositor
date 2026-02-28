-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // gestural // keyboard // keys
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keys - key code type and named constants.
-- |
-- | Provides the KeyCode type and constants for common keys.
-- | Based on W3C UI Events KeyboardEvent.code values.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Gestural.Keyboard.* (all keyboard modules use KeyCode)

module Hydrogen.Schema.Gestural.Keyboard.Keys
  ( -- * Key Code Type
    KeyCode(KeyCode)
  , keyCode
  , unwrapKeyCode
    -- * Navigation Keys
  , keyEnter
  , keyEscape
  , keyBackspace
  , keyTab
  , keySpace
  , keyDelete
  , keyHome
  , keyEnd
  , keyPageUp
  , keyPageDown
  , keyInsert
    -- * Arrow Keys
  , keyArrowUp
  , keyArrowDown
  , keyArrowLeft
  , keyArrowRight
    -- * Function Keys
  , keyF1, keyF2, keyF3, keyF4, keyF5, keyF6
  , keyF7, keyF8, keyF9, keyF10, keyF11, keyF12
    -- * Letter Keys (vim/emacs commands)
  , keyA, keyB, keyC, keyD, keyE, keyF, keyG, keyH, keyI
  , keyJ, keyK, keyL, keyM, keyN, keyO, keyP, keyQ, keyR
  , keyS, keyT, keyU, keyV, keyW, keyX, keyY, keyZ
    -- * Number Keys
  , key0, key1, key2, key3, key4, key5, key6, key7, key8, key9
    -- * Special Keys
  , keyBracketLeft
  , keyBracketRight
  , keySemicolon
  , keyQuote
  , keyBackquote
  , keySlash
  , keyBackslash
  , keyComma
  , keyPeriod
  , keyMinus
  , keyEqual
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // key // code type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physical key code per W3C UI Events spec
-- |
-- | Represents the physical key pressed, independent of keyboard layout.
-- | Based on KeyboardEvent.code values (not KeyboardEvent.key).
newtype KeyCode = KeyCode String

derive instance eqKeyCode :: Eq KeyCode
derive instance ordKeyCode :: Ord KeyCode

instance showKeyCode :: Show KeyCode where
  show (KeyCode code) = code

-- | Create key code from string
keyCode :: String -> KeyCode
keyCode = KeyCode

-- | Extract key code string
unwrapKeyCode :: KeyCode -> String
unwrapKeyCode (KeyCode code) = code

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // navigation // keys
-- ═════════════════════════════════════════════════════════════════════════════

keyEnter :: KeyCode
keyEnter = KeyCode "Enter"

keyEscape :: KeyCode
keyEscape = KeyCode "Escape"

keyBackspace :: KeyCode
keyBackspace = KeyCode "Backspace"

keyTab :: KeyCode
keyTab = KeyCode "Tab"

keySpace :: KeyCode
keySpace = KeyCode "Space"

keyDelete :: KeyCode
keyDelete = KeyCode "Delete"

keyHome :: KeyCode
keyHome = KeyCode "Home"

keyEnd :: KeyCode
keyEnd = KeyCode "End"

keyPageUp :: KeyCode
keyPageUp = KeyCode "PageUp"

keyPageDown :: KeyCode
keyPageDown = KeyCode "PageDown"

keyInsert :: KeyCode
keyInsert = KeyCode "Insert"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // arrow // keys
-- ═════════════════════════════════════════════════════════════════════════════

keyArrowUp :: KeyCode
keyArrowUp = KeyCode "ArrowUp"

keyArrowDown :: KeyCode
keyArrowDown = KeyCode "ArrowDown"

keyArrowLeft :: KeyCode
keyArrowLeft = KeyCode "ArrowLeft"

keyArrowRight :: KeyCode
keyArrowRight = KeyCode "ArrowRight"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // function // keys
-- ═════════════════════════════════════════════════════════════════════════════

keyF1 :: KeyCode
keyF1 = KeyCode "F1"

keyF2 :: KeyCode
keyF2 = KeyCode "F2"

keyF3 :: KeyCode
keyF3 = KeyCode "F3"

keyF4 :: KeyCode
keyF4 = KeyCode "F4"

keyF5 :: KeyCode
keyF5 = KeyCode "F5"

keyF6 :: KeyCode
keyF6 = KeyCode "F6"

keyF7 :: KeyCode
keyF7 = KeyCode "F7"

keyF8 :: KeyCode
keyF8 = KeyCode "F8"

keyF9 :: KeyCode
keyF9 = KeyCode "F9"

keyF10 :: KeyCode
keyF10 = KeyCode "F10"

keyF11 :: KeyCode
keyF11 = KeyCode "F11"

keyF12 :: KeyCode
keyF12 = KeyCode "F12"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // letter // keys
-- ═════════════════════════════════════════════════════════════════════════════

keyA :: KeyCode
keyA = KeyCode "KeyA"

keyB :: KeyCode
keyB = KeyCode "KeyB"

keyC :: KeyCode
keyC = KeyCode "KeyC"

keyD :: KeyCode
keyD = KeyCode "KeyD"

keyE :: KeyCode
keyE = KeyCode "KeyE"

keyF :: KeyCode
keyF = KeyCode "KeyF"

keyG :: KeyCode
keyG = KeyCode "KeyG"

keyH :: KeyCode
keyH = KeyCode "KeyH"

keyI :: KeyCode
keyI = KeyCode "KeyI"

keyJ :: KeyCode
keyJ = KeyCode "KeyJ"

keyK :: KeyCode
keyK = KeyCode "KeyK"

keyL :: KeyCode
keyL = KeyCode "KeyL"

keyM :: KeyCode
keyM = KeyCode "KeyM"

keyN :: KeyCode
keyN = KeyCode "KeyN"

keyO :: KeyCode
keyO = KeyCode "KeyO"

keyP :: KeyCode
keyP = KeyCode "KeyP"

keyQ :: KeyCode
keyQ = KeyCode "KeyQ"

keyR :: KeyCode
keyR = KeyCode "KeyR"

keyS :: KeyCode
keyS = KeyCode "KeyS"

keyT :: KeyCode
keyT = KeyCode "KeyT"

keyU :: KeyCode
keyU = KeyCode "KeyU"

keyV :: KeyCode
keyV = KeyCode "KeyV"

keyW :: KeyCode
keyW = KeyCode "KeyW"

keyX :: KeyCode
keyX = KeyCode "KeyX"

keyY :: KeyCode
keyY = KeyCode "KeyY"

keyZ :: KeyCode
keyZ = KeyCode "KeyZ"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // number // keys
-- ═════════════════════════════════════════════════════════════════════════════

key0 :: KeyCode
key0 = KeyCode "Digit0"

key1 :: KeyCode
key1 = KeyCode "Digit1"

key2 :: KeyCode
key2 = KeyCode "Digit2"

key3 :: KeyCode
key3 = KeyCode "Digit3"

key4 :: KeyCode
key4 = KeyCode "Digit4"

key5 :: KeyCode
key5 = KeyCode "Digit5"

key6 :: KeyCode
key6 = KeyCode "Digit6"

key7 :: KeyCode
key7 = KeyCode "Digit7"

key8 :: KeyCode
key8 = KeyCode "Digit8"

key9 :: KeyCode
key9 = KeyCode "Digit9"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // special // keys
-- ═════════════════════════════════════════════════════════════════════════════

-- | [ - used in vim for bracket commands
keyBracketLeft :: KeyCode
keyBracketLeft = KeyCode "BracketLeft"

-- | ] - used in vim for bracket commands
keyBracketRight :: KeyCode
keyBracketRight = KeyCode "BracketRight"

-- | ; - used in vim for repeat find
keySemicolon :: KeyCode
keySemicolon = KeyCode "Semicolon"

-- | ' - used in vim for marks
keyQuote :: KeyCode
keyQuote = KeyCode "Quote"

-- | ` - backtick, used in vim for marks
keyBackquote :: KeyCode
keyBackquote = KeyCode "Backquote"

-- | / - used in vim for search
keySlash :: KeyCode
keySlash = KeyCode "Slash"

-- | \ - backslash
keyBackslash :: KeyCode
keyBackslash = KeyCode "Backslash"

-- | , - comma, used in vim for repeat reverse find
keyComma :: KeyCode
keyComma = KeyCode "Comma"

-- | . - period, used in vim for repeat command
keyPeriod :: KeyCode
keyPeriod = KeyCode "Period"

-- | - - minus, used in vim for line up
keyMinus :: KeyCode
keyMinus = KeyCode "Minus"

-- | = - equals
keyEqual :: KeyCode
keyEqual = KeyCode "Equal"
