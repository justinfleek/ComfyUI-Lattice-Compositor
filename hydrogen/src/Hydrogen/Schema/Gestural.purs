-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // schema // gestural
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gestural - Pillar 9 of the Hydrogen Schema.
-- |
-- | Input/gesture handling for hyper-responsive interfaces.
-- | Supports web interactions, terminal-style keyboard interactions
-- | (vim/emacs keybindings), and multi-touch gestures.
-- |
-- | ## Sub-modules
-- | - Pointer: Pointer (mouse/pen/touch) events
-- | - Motion: Movement tracking with velocity/acceleration
-- | - Touch: Multi-touch input handling
-- | - Gesture: High-level gesture recognition (tap, swipe, pan)
-- | - Keyboard: Keyboard input, shortcuts, navigation
-- | - Scroll: Scroll state, inertia, snap points
-- | - DragDrop: Drag and drop operations
-- | - Focus: Focus management for accessibility
-- | - Selection: Single, multi, and range selection
-- | - Hover: Hover states and intent detection
-- | - ContextMenu: Right-click and long-press menus
-- | - Arbitration: Gesture conflict resolution
-- | - KeySequence: Vim/emacs-style key sequences
-- | - Trigger: Interactive relationships and easter eggs
-- |
-- | ## Dependents
-- | - Component.* (interactive components)
-- | - Interaction.* (interaction patterns)
-- | - A11y.* (accessibility)

module Hydrogen.Schema.Gestural
  ( -- * Re-exports from Pointer
    module Hydrogen.Schema.Gestural.Pointer
    -- * Re-exports from Motion
  , module Hydrogen.Schema.Gestural.Motion
    -- * Re-exports from Touch
  , module Hydrogen.Schema.Gestural.Touch
    -- * Re-exports from Gesture
  , module Hydrogen.Schema.Gestural.Gesture
    -- * Re-exports from Keyboard
  , module Hydrogen.Schema.Gestural.Keyboard
    -- * Re-exports from Scroll
  , module Hydrogen.Schema.Gestural.Scroll
    -- NOTE: Additional modules are available for direct import:
    -- - Hydrogen.Schema.Gestural.DragDrop (drag and drop operations)
    -- - Hydrogen.Schema.Gestural.Focus (focus management, traps, scopes)
    -- - Hydrogen.Schema.Gestural.Selection (single/multi/range selection)
    -- - Hydrogen.Schema.Gestural.Hover (hover states, intent detection)
    -- - Hydrogen.Schema.Gestural.ContextMenu (right-click menus)
    -- - Hydrogen.Schema.Gestural.Arbitration (gesture conflict resolution)
    -- - Hydrogen.Schema.Gestural.KeySequence (vim/emacs key sequences)
    -- - Hydrogen.Schema.Gestural.Trigger (interactive relationships, easter eggs)
    -- These are not re-exported here due to naming conflicts (itemId, etc.)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // pointer // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Pointer
  ( PointerType(PointerMouse, PointerTouch, PointerPen, PointerUnknown)
  , isMouse
  , isTouch
  , isPen
  , isUnknownPointer
  , pointerTypeFromString
  , PointerPosition
  , pointerPosition
  , clientX
  , clientY
  , pageX
  , pageY
  , screenX
  , screenY
  , offsetX
  , offsetY
  , Pressure(Pressure)
  , pressure
  , noPressure
  , fullPressure
  , unwrapPressure
  , hasPressure
  , TiltX(TiltX)
  , TiltY(TiltY)
  , tiltX
  , tiltY
  , noTilt
  , unwrapTiltX
  , unwrapTiltY
  , Twist(Twist)
  , twist
  , noTwist
  , unwrapTwist
  , PointerSize
  , pointerSize
  , pointPointer
  , pointerWidth
  , pointerHeight
  , pointerRadius
  , PointerState
  , pointerState
  , defaultPointerState
  , mousePointerState
  , touchPointerState
  , penPointerState
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // motion // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Motion
  ( Velocity2D
  , velocity2D
  , zeroVelocity
  , velocityX
  , velocityY
  , velocityMagnitude
  , velocityAngle
  , isMoving
  , isFastMotion
  , Acceleration2D
  , acceleration2D
  , zeroAcceleration
  , accelerationX
  , accelerationY
  , accelerationMagnitude
  , isDecelerating
  , Distance
  , distance
  , distanceBetween
  , unwrapDistance
  , isSignificantDistance
  , Direction
    ( DirectionUp
    , DirectionDown
    , DirectionLeft
    , DirectionRight
    , DirectionUpLeft
    , DirectionUpRight
    , DirectionDownLeft
    , DirectionDownRight
    , DirectionNone
    )
  , directionFromAngle
  , directionFromDelta
  , isHorizontal
  , isVertical
  , oppositeDirection
  , GestureVector
  , gestureVector
  , gestureFromPoints
  , vectorDistance
  , vectorDirection
  , vectorVelocity
  , Momentum
  , momentum
  , applyFriction
  , momentumVelocity
  , momentumPosition
  , isMomentumActive
  , MotionState
  , motionState
  , idleMotion
  , activeMotion
  , updateMotion
  , stopMotion
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // touch // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Touch
  ( TouchPoint
  , touchPoint
  , touchId
  , touchPosition
  , touchPressure
  , touchSize
  , TouchCount(TouchCount)
  , touchCount
  , maxTouches
  , unwrapTouchCount
  , isSingleTouch
  , isMultiTouch
  , PinchState
  , pinchState
  , noPinch
  , pinchScale
  , pinchCenter
  , pinchDistance
  , isPinching
  , isPinchingIn
  , isPinchingOut
  , RotateState
  , rotateState
  , noRotation
  , rotationAngle
  , rotationDelta
  , rotationCenter
  , isRotating
  , TouchState
  , touchState
  , noTouches
  , singleTouchState
  , twoFingerState
  , addTouch
  , removeTouch
  , updateTouch
  , touchPointCount
  , primaryTouch
  , allTouches
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gesture // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Gesture
  ( GesturePhase(Possible, Began, Changed, Ended, Cancelled, Failed)
  , isPossible
  , isBegan
  , isChanged
  , isEnded
  , isCancelled
  , isFailed
  , isActive
  , isTerminal
  , TapCount(TapCount)
  , tapCount
  , singleTap
  , doubleTap
  , tripleTap
  , unwrapTapCount
  , isSingleTap
  , isDoubleTap
  , isTripleTap
  , TapState
  , tapState
  , noTap
  , tapPosition
  , isTapRecognized
  , LongPressThreshold(LongPressThreshold)
  , longPressThreshold
  , defaultLongPressThreshold
  , unwrapLongPressThreshold
  , LongPressState
  , longPressState
  , noLongPress
  , updateLongPressDuration
  , longPressPosition
  , isLongPressTriggered
  , isLongPressActive
  , SwipeDirection(SwipeUp, SwipeDown, SwipeLeft, SwipeRight)
  , isSwipeHorizontal
  , isSwipeVertical
  , oppositeSwipe
  , swipeDirectionFromDelta
  , SwipeVelocityThreshold(SwipeVelocityThreshold)
  , swipeVelocityThreshold
  , defaultSwipeThreshold
  , unwrapSwipeThreshold
  , SwipeState
  , swipeState
  , noSwipe
  , swipeVelocity
  , isSwipeRecognized
  , PanState
  , panState
  , noPan
  , updatePanPosition
  , panTranslation
  , panVelocity
  , isPanning
  , panDistance
  , GestureState
  , initialGestureState
  , resetGestures
  , hasActiveGesture
  , hasCompletedGesture
  , updateTapState
  , updateLongPressState
  , updateSwipeState
  , updatePanState
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // keyboard // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Keyboard
  ( KeyCode(KeyCode)
  , keyCode
  , unwrapKeyCode
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
  , keyArrowUp
  , keyArrowDown
  , keyArrowLeft
  , keyArrowRight
  , keyF1, keyF2, keyF3, keyF4, keyF5, keyF6
  , keyF7, keyF8, keyF9, keyF10, keyF11, keyF12
  , keyA, keyB, keyC, keyD, keyE, keyF, keyG, keyH, keyI
  , keyJ, keyK, keyL, keyM, keyN, keyO, keyP, keyQ, keyR
  , keyS, keyT, keyU, keyV, keyW, keyX, keyY, keyZ
  , key0, key1, key2, key3, key4, key5, key6, key7, key8, key9
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
  , ModifierState
  , noModifiers
  , ctrlOnly
  , altOnly
  , shiftOnly
  , metaOnly
  , hasCtrlOrCmd
  , hasAnyModifier
  , onlyShift
  , onlyCtrl
  , onlyAlt
  , onlyMeta
  , ctrlShift
  , altShift
  , ctrlAlt
  , ctrlAltShift
  , hasPlatformModifier
  , KeyEventType(KeyDown, KeyUp, KeyPress)
  , isKeyDown
  , isKeyUp
  , isKeyPress
  , KeyEvent
  , keyEvent
  , keyEventFull
  , eventCode
  , eventKey
  , eventModifiers
  , isRepeat
  , isPrintableKey
  , isModifierKey
  , isFunctionKey
  , isNavigationKey
  , Shortcut
  , shortcut
  , simpleShortcut
  , ctrlShortcut
  , ctrlShiftShortcut
  , altShortcut
  , altShiftShortcut
  , metaShortcut
  , metaShiftShortcut
  , matchesShortcut
  , matchesShortcutLoose
  , shortcutCopy
  , shortcutCut
  , shortcutPaste
  , shortcutUndo
  , shortcutRedo
  , shortcutSelectAll
  , shortcutSave
  , shortcutFind
  , shortcutClose
  , shortcutNew
  , shortcutOpen
  , shortcutRedoY
  , ArrowDirection(ArrowUp, ArrowDown, ArrowLeft, ArrowRight)
  , isHorizontalArrow
  , isVerticalArrow
  , arrowFromCode
  , arrowFromEvent
  , oppositeArrow
  , TabDirection(TabForward, TabBackward)
  , tabDirectionFromEvent
  , oppositeTab
  , VimMovement(VimUp, VimDown, VimLeft, VimRight)
  , vimFromCode
  , vimFromEvent
  , vimToArrow
  , FocusAction(FocusNext, FocusPrev, FocusFirst, FocusLast, FocusParent)
  , focusActionFromEvent
  , KeyboardState
  , initialKeyboardState
  , stateModifiers
  , stateLastEvent
  , stateIsTyping
  , stateTimestamp
  , updateKeyboardState
  , clearKeyboardState
  , resetModifiers
  , hasActiveModifiers
  , timeSinceLastEvent
  , isIdle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // scroll // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Scroll
  ( ScrollPosition
  , scrollPosition
  , scrollX
  , scrollY
  , scrollTop
  , scrollLeft
  , addScrollPosition
  , ScrollDelta
  , scrollDelta
  , deltaPixel
  , deltaLine
  , deltaPage
  , normalizeDelta
  , isScrollingHorizontal
  , isScrollingVertical
  , ScrollProgress
  , scrollProgress
  , progressX
  , progressY
  , progressFromPosition
  , isAtStart
  , isAtEnd
  , isNearStart
  , isNearEnd
  , ScrollBounds
  , scrollBounds
  , clampToScrollBounds
  , canScrollUp
  , canScrollDown
  , canScrollLeft
  , canScrollRight
  , scrollableHeight
  , scrollableWidth
  , OverscrollBehavior(OverscrollAuto, OverscrollContain, OverscrollNone)
  , OverscrollState
  , noOverscroll
  , overscrollAmount
  , isOverscrolling
  , applyOverscrollResistance
  , SnapAlignment(SnapStart, SnapCenter, SnapEnd)
  , SnapType(SnapMandatory, SnapProximity)
  , SnapPoint
  , snapPoint
  , findNearestSnap
  , shouldSnap
  , ScrollState
  , initialScrollState
  , updateScrollPosition
  , updateScrollVelocity
  , applyScrollDelta
  , isScrolling
  , scrollVelocity
  )
