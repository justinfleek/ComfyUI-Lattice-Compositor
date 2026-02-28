-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // ui // button
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Button Component — Pure Element Version
-- |
-- | Renders buttons using the pure Element abstraction. Can be compiled to
-- | any target (Halogen, Static HTML, etc.).
-- |
-- | ## Usage with Halogen
-- |
-- | ```purescript
-- | import Hydrogen.UI.Button as Button
-- | import Hydrogen.Target.Halogen as TH
-- |
-- | -- Define button as pure Element
-- | myButton :: Button.Element Action
-- | myButton = Button.button
-- |   [ Button.variant Button.Primary
-- |   , Button.onClick MyAction
-- |   ]
-- |   [ E.text "Click me" ]
-- |
-- | -- Convert to Halogen HTML in render
-- | render :: State -> H.ComponentHTML Action Slots m
-- | render _ = TH.toHalogen myButton
-- | ```
-- |
-- | ## Usage for Static Rendering
-- |
-- | ```purescript
-- | import Hydrogen.UI.Button as Button
-- | import Hydrogen.Target.Static as TS
-- |
-- | html :: String
-- | html = TS.render (Button.button [ Button.variant Button.Primary ] [ E.text "Submit" ])
-- | ```
module Hydrogen.UI.Button
  ( -- * Button Component
    button
  , buttonLink
  
  -- * Configuration
  , ButtonConfig
  , defaultConfig
  
  -- * Config Modifiers
  , variant
  , size
  , disabled
  , loading
  , shadow
  , className
  , onClick
  , type_
  
  -- * Variants
  , ButtonVariant(Primary, Secondary, Destructive, Outline, Ghost, Link)
  
  -- * Sizes
  , ButtonSize(Sm, Md, Lg, Icon)
  
  -- * Types
  , ButtonType(TypeButton, TypeSubmit, TypeReset)
  ) where

import Prelude
  ( class Eq
  , (<>)
  , (||)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button visual variants
data ButtonVariant
  = Primary
  | Secondary
  | Destructive
  | Outline
  | Ghost
  | Link

derive instance eqButtonVariant :: Eq ButtonVariant

-- | Get Tailwind classes for variant
variantClasses :: ButtonVariant -> String
variantClasses = case _ of
  Primary ->
    "bg-primary text-primary-foreground hover:bg-primary-foreground hover:text-primary border border-transparent hover:border-primary"
  Secondary ->
    "bg-secondary text-secondary-foreground hover:bg-primary hover:text-primary-foreground"
  Destructive ->
    "bg-destructive text-destructive-foreground hover:bg-destructive-foreground hover:text-destructive border border-transparent hover:border-destructive"
  Outline ->
    "border border-white/20 bg-transparent hover:bg-white/5 hover:border-white/40"
  Ghost ->
    "hover:bg-accent hover:text-accent-foreground"
  Link ->
    "text-primary underline-offset-4 hover:underline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button sizes
data ButtonSize
  = Sm
  | Md
  | Lg
  | Icon

derive instance eqButtonSize :: Eq ButtonSize

-- | Get Tailwind classes for size
sizeClasses :: ButtonSize -> String
sizeClasses = case _ of
  Sm -> "h-9 rounded-md px-3"
  Md -> "h-10 px-4 py-2"
  Lg -> "h-11 rounded-md px-8"
  Icon -> "h-10 w-10"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTML button type attribute
data ButtonType
  = TypeButton
  | TypeSubmit
  | TypeReset

derive instance eqButtonType :: Eq ButtonType

-- | Convert ButtonType to string value
buttonTypeStr :: ButtonType -> String
buttonTypeStr = case _ of
  TypeButton -> "button"
  TypeSubmit -> "submit"
  TypeReset -> "reset"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button configuration
-- |
-- | The `msg` type parameter is the message produced when the button is clicked.
type ButtonConfig msg =
  { variant :: ButtonVariant
  , size :: ButtonSize
  , disabled :: Boolean
  , loading :: Boolean
  , shadow :: Boolean
  , className :: String
  , onClick :: Maybe msg
  , type_ :: ButtonType
  }

-- | Default button configuration
defaultConfig :: forall msg. ButtonConfig msg
defaultConfig =
  { variant: Primary
  , size: Md
  , disabled: false
  , loading: false
  , shadow: false
  , className: ""
  , onClick: Nothing
  , type_: TypeButton
  }

-- | Configuration modifier type
type ConfigMod msg = ButtonConfig msg -> ButtonConfig msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // config // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set button variant
variant :: forall msg. ButtonVariant -> ConfigMod msg
variant v config = config { variant = v }

-- | Set button size
size :: forall msg. ButtonSize -> ConfigMod msg
size s config = config { size = s }

-- | Set disabled state
disabled :: forall msg. Boolean -> ConfigMod msg
disabled d config = config { disabled = d }

-- | Set loading state (also disables the button)
loading :: forall msg. Boolean -> ConfigMod msg
loading l config = config { loading = l }

-- | Enable drop shadow
shadow :: forall msg. Boolean -> ConfigMod msg
shadow s config = config { shadow = s }

-- | Add custom CSS class
className :: forall msg. String -> ConfigMod msg
className c config = config { className = config.className <> " " <> c }

-- | Set click handler
-- |
-- | When clicked, the button will produce this message.
onClick :: forall msg. msg -> ConfigMod msg
onClick msg config = config { onClick = Just msg }

-- | Set button type (button, submit, reset)
type_ :: forall msg. ButtonType -> ConfigMod msg
type_ t config = config { type_ = t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base button classes (Tailwind)
baseClasses :: String
baseClasses =
  "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-all duration-150 ease-out focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 active:scale-[0.98]"

-- | Shadow classes for elevated buttons
shadowClasses :: String
shadowClasses =
  "shadow-lg shadow-black/25 hover:shadow-xl hover:shadow-black/30"

-- | Render a button as a pure Element
-- |
-- | ```purescript
-- | button [ variant Primary, onClick Submit ] [ E.text "Submit" ]
-- | ```
button :: forall msg. Array (ConfigMod msg) -> Array (E.Element msg) -> E.Element msg
button mods children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    shadowClass = if config.shadow then shadowClasses else ""
    loadingClass = if config.loading then "opacity-70 cursor-wait" else ""
    allClasses = baseClasses 
      <> " " <> variantClasses config.variant 
      <> " " <> sizeClasses config.size 
      <> " " <> shadowClass 
      <> " " <> loadingClass
      <> " " <> config.className
    
    -- Build attributes
    baseAttrs = 
      [ E.class_ allClasses
      , E.type_ (buttonTypeStr config.type_)
      , E.disabled (config.disabled || config.loading)
      ]
    
    -- Add click handler if present
    attrs = case config.onClick of
      Just msg -> baseAttrs <> [ E.onClick msg ]
      Nothing -> baseAttrs
    
    -- Add loading spinner if loading
    content = if config.loading
      then [ loadingSpinner, E.span_ [ E.class_ "ml-2" ] children ]
      else children
  in
    E.button_ attrs content

-- | Render a button-styled link as a pure Element
-- |
-- | ```purescript
-- | buttonLink [ variant Secondary ] "/dashboard" [ E.text "Dashboard" ]
-- | ```
buttonLink :: forall msg. Array (ConfigMod msg) -> String -> Array (E.Element msg) -> E.Element msg
buttonLink mods href children =
  let
    config = foldl (\c f -> f c) defaultConfig mods
    allClasses = baseClasses 
      <> " " <> variantClasses config.variant 
      <> " " <> sizeClasses config.size 
      <> " " <> config.className
  in
    E.a_ 
      [ E.class_ allClasses
      , E.href href
      ]
      children

-- | Loading spinner element
loadingSpinner :: forall msg. E.Element msg
loadingSpinner =
  E.div_
    [ E.class_ "w-4 h-4 animate-spin rounded-full border-2 border-current border-t-transparent" ]
    []
