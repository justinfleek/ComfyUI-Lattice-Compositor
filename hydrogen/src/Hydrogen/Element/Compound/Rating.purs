-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // rating
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Rating Component
-- |
-- | Interactive rating component with customizable icons and states.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Rating as Rating
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic 5-star rating
-- | Rating.rating
-- |   [ Rating.ratingValue 3.0
-- |   , Rating.onRatingChange (\n -> SetRating n)
-- |   ]
-- |
-- | -- Half-star support
-- | Rating.rating
-- |   [ Rating.ratingValue 3.5
-- |   , Rating.allowHalf true
-- |   ]
-- |
-- | -- Custom max and icon
-- | Rating.rating
-- |   [ Rating.ratingValue 4.0
-- |   , Rating.maxValue 10
-- |   , Rating.icon Rating.Heart
-- |   ]
-- |
-- | -- Read-only display
-- | Rating.rating
-- |   [ Rating.ratingValue 4.5
-- |   , Rating.isReadOnly true
-- |   ]
-- | ```
module Hydrogen.Element.Compound.Rating
  ( -- * Rating Component
    rating
  , ratingItem
    -- * Props
  , RatingProps
  , RatingProp
  , defaultProps
    -- * Prop Builders
  , ratingValue
  , maxValue
  , allowHalf
  , icon
  , ratingSize
  , activeColor
  , inactiveColor
  , isReadOnly
  , isDisabled
  , clearable
  , ratingClassName
  , onRatingChange
    -- * Types
  , RatingIcon(Star, Heart, Emoji, Custom)
  , RatingSize(Small, Medium, Large)
  , FillLevel(Empty, Half, Full)
  ) where

import Prelude
  ( class Eq
  , show
  , not
  , map
  , negate
  , (<>)
  , (>=)
  , (-)
  , (&&)
  , (==)
  )

import Data.Array (foldl, range)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icon type for rating
data RatingIcon
  = Star
  | Heart
  | Emoji
  | Custom String  -- Custom character

derive instance eqRatingIcon :: Eq RatingIcon

-- | Rating size variants
data RatingSize
  = Small
  | Medium
  | Large

derive instance eqRatingSize :: Eq RatingSize

-- | Fill level for icons
data FillLevel 
  = Empty 
  | Half 
  | Full

derive instance eqFillLevel :: Eq FillLevel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

type RatingProps msg =
  { value :: Number
  , maxValue :: Int
  , allowHalf :: Boolean
  , icon :: RatingIcon
  , size :: RatingSize
  , activeColor :: String
  , inactiveColor :: String
  , readOnly :: Boolean
  , disabled :: Boolean
  , clearable :: Boolean
  , className :: String
  , onChange :: Maybe (Number -> msg)
  }

type RatingProp msg = RatingProps msg -> RatingProps msg

defaultProps :: forall msg. RatingProps msg
defaultProps =
  { value: 0.0
  , maxValue: 5
  , allowHalf: false
  , icon: Star
  , size: Medium
  , activeColor: "text-yellow-400"
  , inactiveColor: "text-gray-300"
  , readOnly: false
  , disabled: false
  , clearable: false
  , className: ""
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set rating value (0 to maxValue)
ratingValue :: forall msg. Number -> RatingProp msg
ratingValue v props = props { value = v }

-- | Set maximum rating value
maxValue :: forall msg. Int -> RatingProp msg
maxValue m props = props { maxValue = m }

-- | Allow half values
allowHalf :: forall msg. Boolean -> RatingProp msg
allowHalf h props = props { allowHalf = h }

-- | Set icon type
icon :: forall msg. RatingIcon -> RatingProp msg
icon ic props = props { icon = ic }

-- | Set size
ratingSize :: forall msg. RatingSize -> RatingProp msg
ratingSize s props = props { size = s }

-- | Set active (filled) color
activeColor :: forall msg. String -> RatingProp msg
activeColor c props = props { activeColor = c }

-- | Set inactive (empty) color
inactiveColor :: forall msg. String -> RatingProp msg
inactiveColor c props = props { inactiveColor = c }

-- | Set read-only state
isReadOnly :: forall msg. Boolean -> RatingProp msg
isReadOnly r props = props { readOnly = r }

-- | Set disabled state
isDisabled :: forall msg. Boolean -> RatingProp msg
isDisabled d props = props { disabled = d }

-- | Allow clearing (clicking active to clear)
clearable :: forall msg. Boolean -> RatingProp msg
clearable c props = props { clearable = c }

-- | Add custom class
ratingClassName :: forall msg. String -> RatingProp msg
ratingClassName c props = props { className = props.className <> " " <> c }

-- | Set change handler
onRatingChange :: forall msg. (Number -> msg) -> RatingProp msg
onRatingChange handler props = props { onChange = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get size classes
sizeClasses :: RatingSize -> String
sizeClasses = case _ of
  Small -> "w-4 h-4"
  Medium -> "w-6 h-6"
  Large -> "w-8 h-8"

-- | Get gap classes based on size
gapClasses :: RatingSize -> String
gapClasses = case _ of
  Small -> "gap-0.5"
  Medium -> "gap-1"
  Large -> "gap-1.5"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Main rating component
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
rating :: forall msg. Array (RatingProp msg) -> E.Element msg
rating propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    displayValue = props.value
    items = range 1 props.maxValue
    isInteractive = not props.readOnly && not props.disabled
  in
    E.div_
      [ E.classes 
          [ "inline-flex items-center"
          , gapClasses props.size
          , if props.disabled then "opacity-50 cursor-not-allowed" else ""
          , props.className
          ]
      , E.role "radiogroup"
      , E.ariaLabel ("Rating: " <> show props.value <> " out of " <> show props.maxValue)
      ]
      (map (\idx -> ratingItem props idx displayValue isInteractive) items)

-- | Single rating item (star/heart/emoji)
ratingItem :: forall msg. RatingProps msg -> Int -> Number -> Boolean -> E.Element msg
ratingItem props idx displayValue isInteractive =
  let
    idxNum = toNumber idx
    fillLevel = 
      if displayValue >= idxNum 
        then Full
        else if props.allowHalf && displayValue >= idxNum - 0.5 
          then Half
          else Empty
    
    handleClick :: Maybe msg
    handleClick = 
      if isInteractive 
        then case props.onChange of
          Just handler -> 
            let 
              newValue = 
                if props.clearable && props.value == idxNum 
                  then 0.0 
                  else idxNum
            in Just (handler newValue)
          Nothing -> Nothing
        else Nothing
    
    handleHalfClick :: Maybe msg
    handleHalfClick =
      if isInteractive && props.allowHalf
        then case props.onChange of
          Just handler -> Just (handler (idxNum - 0.5))
          Nothing -> Nothing
        else Nothing
    
    clickHandler = case handleClick of
      Just h -> [ E.onClick h ]
      Nothing -> []
    
    halfClickHandler = case handleHalfClick of
      Just h -> [ E.onClick h ]
      Nothing -> []
  in
    E.div_
      [ E.classes 
          [ "relative cursor-pointer"
          , sizeClasses props.size
          , if not isInteractive then "cursor-default" else "hover:scale-110 transition-transform"
          ]
      , E.role "radio"
      , E.attr "aria-checked" (show (props.value >= idxNum))
      , E.tabIndex (if isInteractive && idx == 1 then 0 else (-1))
      ]
      [ -- Full icon (background)
        E.div_
          [ E.classes [ "absolute inset-0", props.inactiveColor ] ]
          [ renderIcon props.icon Empty ]
        -- Filled icon (foreground with clipping for half)
      , case fillLevel of
          Empty -> E.empty
          Full -> 
            E.div_
              ([ E.classes [ "absolute inset-0", props.activeColor ] ] <> clickHandler)
              [ renderIcon props.icon Full ]
          Half ->
            E.div_
              [ E.classes [ "absolute inset-0 overflow-hidden", props.activeColor ]
              , E.style "width" "50%"
              ]
              [ renderIcon props.icon Full ]
        -- Click zones for half-star support
      , if props.allowHalf && isInteractive
          then 
            E.div_
              [ E.class_ "absolute inset-0 flex" ]
              [ E.div_ ([ E.class_ "w-1/2 h-full" ] <> halfClickHandler) []
              , E.div_ ([ E.class_ "w-1/2 h-full" ] <> clickHandler) []
              ]
          else 
            E.div_ ([ E.class_ "absolute inset-0" ] <> clickHandler) []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render icon based on type
renderIcon :: forall msg. RatingIcon -> FillLevel -> E.Element msg
renderIcon iconType fillLevel = case iconType of
  Star -> starIcon fillLevel
  Heart -> heartIcon fillLevel
  Emoji -> emojiIcon fillLevel
  Custom char -> E.span_ [ E.class_ "text-2xl select-none" ] [ E.text char ]

-- | Star icon
starIcon :: forall msg. FillLevel -> E.Element msg
starIcon fillLevel =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" (if fillLevel == Empty then "none" else "currentColor")
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.class_ "w-full h-full"
    ]
    [ E.svgElement "polygon"
        [ E.attr "points" "12 2 15.09 8.26 22 9.27 17 14.14 18.18 21.02 12 17.77 5.82 21.02 7 14.14 2 9.27 8.91 8.26 12 2" ]
        []
    ]

-- | Heart icon
heartIcon :: forall msg. FillLevel -> E.Element msg
heartIcon fillLevel =
  E.svg_
    [ E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" (if fillLevel == Empty then "none" else "currentColor")
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.class_ "w-full h-full"
    ]
    [ E.path_
        [ E.attr "d" "M20.84 4.61a5.5 5.5 0 0 0-7.78 0L12 5.67l-1.06-1.06a5.5 5.5 0 0 0-7.78 7.78l1.06 1.06L12 21.23l7.78-7.78 1.06-1.06a5.5 5.5 0 0 0 0-7.78z" ]
    ]

-- | Emoji icon (face expressions)
emojiIcon :: forall msg. FillLevel -> E.Element msg
emojiIcon fillLevel =
  let
    emoji = case fillLevel of
      Empty -> "😶"
      Half -> "🙂"
      Full -> "😊"
  in
    E.span_ 
      [ E.class_ "text-2xl select-none leading-none" ] 
      [ E.text emoji ]
