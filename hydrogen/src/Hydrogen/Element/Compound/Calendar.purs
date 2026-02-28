-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // compound // calendar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Calendar — Schema-native date selection component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms. It renders a monthly
-- | calendar grid with navigation and date selection capabilities.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property               | Pillar     | Type                      | CSS Output              |
-- | |------------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor        | Color      | Color.RGB                 | calendar background     |
-- | | borderColor            | Color      | Color.RGB                 | calendar border         |
-- | | textColor              | Color      | Color.RGB                 | default text color      |
-- | | headerColor            | Color      | Color.RGB                 | month/year header       |
-- | | dayHeaderColor         | Color      | Color.RGB                 | day name headers        |
-- | | selectedColor          | Color      | Color.RGB                 | selected date bg        |
-- | | selectedTextColor      | Color      | Color.RGB                 | selected date text      |
-- | | rangeColor             | Color      | Color.RGB                 | date range bg           |
-- | | todayRingColor         | Color      | Color.RGB                 | today indicator ring    |
-- | | hoverColor             | Color      | Color.RGB                 | hover background        |
-- | | disabledColor          | Color      | Color.RGB                 | disabled date color     |
-- | | borderRadius           | Geometry   | Geometry.Radius           | calendar rounding       |
-- | | dayCellRadius          | Geometry   | Geometry.Radius           | day cell rounding       |
-- | | padding                | Dimension  | Device.Pixel              | internal padding        |
-- | | cellSize               | Dimension  | Device.Pixel              | day cell size           |
-- | | gap                    | Dimension  | Device.Pixel              | spacing between weeks   |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Calendar as Calendar
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic calendar
-- | Calendar.calendar
-- |   [ Calendar.viewMonth 3
-- |   , Calendar.viewYear 2026
-- |   , Calendar.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- With selected date and brand colors
-- | Calendar.calendar
-- |   [ Calendar.viewMonth state.month
-- |   , Calendar.viewYear state.year
-- |   , Calendar.selected (Just state.selectedDate)
-- |   , Calendar.selectedColor brand.primaryColor
-- |   , Calendar.selectedTextColor brand.onPrimaryColor
-- |   , Calendar.borderRadius brand.containerRadius
-- |   , Calendar.onSelect HandleDateSelect
-- |   ]
-- |
-- | -- Date range selection
-- | Calendar.calendar
-- |   [ Calendar.selectionMode Calendar.Range
-- |   , Calendar.rangeStart state.startDate
-- |   , Calendar.rangeEnd state.endDate
-- |   , Calendar.rangeColor brand.primaryColorLight
-- |   , Calendar.onRangeSelect HandleRangeSelect
-- |   ]
-- | ```

module Hydrogen.Element.Compound.Calendar
  ( -- * Component
    calendar
  , calendarWithNav
  
  -- * Types
  , CalendarDate
  , DateRange
  , SelectionMode(Single, Range, Multiple)
  , WeekStart(Sunday, Monday)
  , MonthDay(DayEmpty, DayDate)
  , MonthWeek
  , MonthGrid
  , Locale(EnUS, EnGB, De, Fr, Es, Ja, Zh)
  
  -- * Locale Helpers
  , monthName
  
  -- * Props
  , CalendarProps
  , CalendarProp
  , defaultProps
  
  -- * View State Props
  , viewMonth
  , viewYear
  
  -- * Selection Props
  , selected
  , selectionMode
  , rangeStart
  , rangeEnd
  , multiSelected
  
  -- * Constraint Props
  , minDate
  , maxDate
  , disabledDates
  
  -- * Display Props
  , weekStartsOn
  , showWeekNumbers
  
  -- * Color Atoms
  , backgroundColor
  , borderColor
  , textColor
  , headerColor
  , dayHeaderColor
  , selectedColor
  , selectedTextColor
  , rangeColor
  , todayRingColor
  , hoverColor
  , disabledColor
  , navButtonColor
  , navButtonHoverColor
  
  -- * Geometry Atoms
  , borderRadius
  , dayCellRadius
  , navButtonRadius
  
  -- * Dimension Atoms
  , padding
  , cellSize
  , gap
  , borderWidth
  
  -- * Typography Atoms
  , headerFontSize
  , headerFontWeight
  , dayHeaderFontSize
  , dayHeaderFontWeight
  , dayFontSize
  , dayFontWeight
  
  -- * Behavior Props
  , onSelect
  , onRangeSelect
  , onMultiSelect
  , onMonthChange
  , onPrevMonth
  , onNextMonth
  
  -- * Date Operations (pure Gregorian arithmetic)
  , isLeapYear
  , getDaysInMonth
  , dayOfWeek
  , getFirstDayOfMonth
  , compareDates
  , sameDate
  , addDays
  , addMonths
  , getWeekNumber
  
  -- * Grid Building
  , buildMonthGrid
  ) where

import Prelude
  ( class Eq
  , class Show
  , const
  , map
  , negate
  , not
  , otherwise
  , show
  , (&&)
  , (+)
  , (-)
  , (<)
  , (<>)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (||)
  , (/)
  , (*)
  )

import Data.Array (foldl, snoc)
import Data.Array as Array
import Data.Int (rem)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A date represented as year, month (1-12), and day
type CalendarDate =
  { year :: Int
  , month :: Int  -- 1-indexed: 1 = January, 12 = December
  , day :: Int
  }

-- | A date range with start and end dates
type DateRange =
  { start :: CalendarDate
  , end :: CalendarDate
  }

-- | Selection mode for the calendar
data SelectionMode
  = Single    -- ^ Select a single date
  | Range     -- ^ Select a date range (start to end)
  | Multiple  -- ^ Select multiple individual dates

derive instance eqSelectionMode :: Eq SelectionMode

instance showSelectionMode :: Show SelectionMode where
  show Single = "Single"
  show Range = "Range"
  show Multiple = "Multiple"

-- | Which day the week starts on
data WeekStart
  = Sunday
  | Monday

derive instance eqWeekStart :: Eq WeekStart

instance showWeekStart :: Show WeekStart where
  show Sunday = "Sunday"
  show Monday = "Monday"

-- | Convert WeekStart to day index (0 = Sunday)
weekStartIndex :: WeekStart -> Int
weekStartIndex Sunday = 0
weekStartIndex Monday = 1

-- | Locale for date formatting
data Locale
  = EnUS   -- English (United States)
  | EnGB   -- English (United Kingdom)
  | De     -- German
  | Fr     -- French
  | Es     -- Spanish
  | Ja     -- Japanese
  | Zh     -- Chinese

derive instance eqLocale :: Eq Locale

instance showLocale :: Show Locale where
  show EnUS = "en-US"
  show EnGB = "en-GB"
  show De = "de"
  show Fr = "fr"
  show Es = "es"
  show Ja = "ja"
  show Zh = "zh"

-- | A day cell in the month grid
data MonthDay
  = DayEmpty                           -- Empty cell (padding)
  | DayDate CalendarDate               -- A date cell

derive instance eqMonthDay :: Eq MonthDay

-- | A week row in the month grid
type MonthWeek =
  { weekNumber :: Int
  , days :: Array MonthDay
  }

-- | The complete month grid
type MonthGrid =
  { year :: Int
  , month :: Int
  , weeks :: Array MonthWeek
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calendar properties
-- |
-- | All visual properties accept Schema atoms directly.
type CalendarProps msg =
  { -- View state
    viewMonth :: Int              -- Currently viewed month (1-12)
  , viewYear :: Int               -- Currently viewed year
  
  -- Selection state
  , selected :: Maybe CalendarDate
  , selectionMode :: SelectionMode
  , rangeStart :: Maybe CalendarDate
  , rangeEnd :: Maybe CalendarDate
  , multiSelected :: Array CalendarDate
  
  -- Constraints
  , minDate :: Maybe CalendarDate
  , maxDate :: Maybe CalendarDate
  , disabledDates :: CalendarDate -> Boolean
  
  -- Display options
  , weekStartsOn :: WeekStart
  , showWeekNumbers :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , headerColor :: Maybe Color.RGB
  , dayHeaderColor :: Maybe Color.RGB
  , selectedColor :: Maybe Color.RGB
  , selectedTextColor :: Maybe Color.RGB
  , rangeColor :: Maybe Color.RGB
  , todayRingColor :: Maybe Color.RGB
  , hoverColor :: Maybe Color.RGB
  , disabledColor :: Maybe Color.RGB
  , navButtonColor :: Maybe Color.RGB
  , navButtonHoverColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Radius
  , dayCellRadius :: Maybe Geometry.Radius
  , navButtonRadius :: Maybe Geometry.Radius
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , cellSize :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  
  -- Typography atoms
  , headerFontSize :: Maybe FontSize.FontSize
  , headerFontWeight :: Maybe FontWeight.FontWeight
  , dayHeaderFontSize :: Maybe FontSize.FontSize
  , dayHeaderFontWeight :: Maybe FontWeight.FontWeight
  , dayFontSize :: Maybe FontSize.FontSize
  , dayFontWeight :: Maybe FontWeight.FontWeight
  
  -- Behavior
  , onSelect :: Maybe (CalendarDate -> msg)
  , onRangeSelect :: Maybe (DateRange -> msg)
  , onMultiSelect :: Maybe (Array CalendarDate -> msg)
  , onMonthChange :: Maybe ({ year :: Int, month :: Int } -> msg)
  , onPrevMonth :: Maybe msg
  , onNextMonth :: Maybe msg
  }

-- | Property modifier function
type CalendarProp msg = CalendarProps msg -> CalendarProps msg

-- | Default properties
defaultProps :: forall msg. CalendarProps msg
defaultProps =
  { viewMonth: 1
  , viewYear: 2024
  , selected: Nothing
  , selectionMode: Single
  , rangeStart: Nothing
  , rangeEnd: Nothing
  , multiSelected: []
  , minDate: Nothing
  , maxDate: Nothing
  , disabledDates: const false
  , weekStartsOn: Sunday
  , showWeekNumbers: false
  , backgroundColor: Nothing
  , borderColor: Nothing
  , textColor: Nothing
  , headerColor: Nothing
  , dayHeaderColor: Nothing
  , selectedColor: Nothing
  , selectedTextColor: Nothing
  , rangeColor: Nothing
  , todayRingColor: Nothing
  , hoverColor: Nothing
  , disabledColor: Nothing
  , navButtonColor: Nothing
  , navButtonHoverColor: Nothing
  , borderRadius: Nothing
  , dayCellRadius: Nothing
  , navButtonRadius: Nothing
  , padding: Nothing
  , cellSize: Nothing
  , gap: Nothing
  , borderWidth: Nothing
  , headerFontSize: Nothing
  , headerFontWeight: Nothing
  , dayHeaderFontSize: Nothing
  , dayHeaderFontWeight: Nothing
  , dayFontSize: Nothing
  , dayFontWeight: Nothing
  , onSelect: Nothing
  , onRangeSelect: Nothing
  , onMultiSelect: Nothing
  , onMonthChange: Nothing
  , onPrevMonth: Nothing
  , onNextMonth: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- View state props

viewMonth :: forall msg. Int -> CalendarProp msg
viewMonth m props = props { viewMonth = m }

viewYear :: forall msg. Int -> CalendarProp msg
viewYear y props = props { viewYear = y }

-- Selection props

selected :: forall msg. Maybe CalendarDate -> CalendarProp msg
selected d props = props { selected = d }

selectionMode :: forall msg. SelectionMode -> CalendarProp msg
selectionMode m props = props { selectionMode = m }

rangeStart :: forall msg. Maybe CalendarDate -> CalendarProp msg
rangeStart d props = props { rangeStart = d }

rangeEnd :: forall msg. Maybe CalendarDate -> CalendarProp msg
rangeEnd d props = props { rangeEnd = d }

multiSelected :: forall msg. Array CalendarDate -> CalendarProp msg
multiSelected dates props = props { multiSelected = dates }

-- Constraint props

minDate :: forall msg. CalendarDate -> CalendarProp msg
minDate d props = props { minDate = Just d }

maxDate :: forall msg. CalendarDate -> CalendarProp msg
maxDate d props = props { maxDate = Just d }

disabledDates :: forall msg. (CalendarDate -> Boolean) -> CalendarProp msg
disabledDates pred props = props { disabledDates = pred }

-- Display props

weekStartsOn :: forall msg. WeekStart -> CalendarProp msg
weekStartsOn ws props = props { weekStartsOn = ws }

showWeekNumbers :: forall msg. Boolean -> CalendarProp msg
showWeekNumbers b props = props { showWeekNumbers = b }

-- Color atom props

backgroundColor :: forall msg. Color.RGB -> CalendarProp msg
backgroundColor c props = props { backgroundColor = Just c }

borderColor :: forall msg. Color.RGB -> CalendarProp msg
borderColor c props = props { borderColor = Just c }

textColor :: forall msg. Color.RGB -> CalendarProp msg
textColor c props = props { textColor = Just c }

headerColor :: forall msg. Color.RGB -> CalendarProp msg
headerColor c props = props { headerColor = Just c }

dayHeaderColor :: forall msg. Color.RGB -> CalendarProp msg
dayHeaderColor c props = props { dayHeaderColor = Just c }

selectedColor :: forall msg. Color.RGB -> CalendarProp msg
selectedColor c props = props { selectedColor = Just c }

selectedTextColor :: forall msg. Color.RGB -> CalendarProp msg
selectedTextColor c props = props { selectedTextColor = Just c }

rangeColor :: forall msg. Color.RGB -> CalendarProp msg
rangeColor c props = props { rangeColor = Just c }

todayRingColor :: forall msg. Color.RGB -> CalendarProp msg
todayRingColor c props = props { todayRingColor = Just c }

hoverColor :: forall msg. Color.RGB -> CalendarProp msg
hoverColor c props = props { hoverColor = Just c }

disabledColor :: forall msg. Color.RGB -> CalendarProp msg
disabledColor c props = props { disabledColor = Just c }

navButtonColor :: forall msg. Color.RGB -> CalendarProp msg
navButtonColor c props = props { navButtonColor = Just c }

navButtonHoverColor :: forall msg. Color.RGB -> CalendarProp msg
navButtonHoverColor c props = props { navButtonHoverColor = Just c }

-- Geometry atom props

borderRadius :: forall msg. Geometry.Radius -> CalendarProp msg
borderRadius r props = props { borderRadius = Just r }

dayCellRadius :: forall msg. Geometry.Radius -> CalendarProp msg
dayCellRadius r props = props { dayCellRadius = Just r }

navButtonRadius :: forall msg. Geometry.Radius -> CalendarProp msg
navButtonRadius r props = props { navButtonRadius = Just r }

-- Dimension atom props

padding :: forall msg. Device.Pixel -> CalendarProp msg
padding p props = props { padding = Just p }

cellSize :: forall msg. Device.Pixel -> CalendarProp msg
cellSize s props = props { cellSize = Just s }

gap :: forall msg. Device.Pixel -> CalendarProp msg
gap g props = props { gap = Just g }

borderWidth :: forall msg. Device.Pixel -> CalendarProp msg
borderWidth w props = props { borderWidth = Just w }

-- Typography atom props

headerFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
headerFontSize s props = props { headerFontSize = Just s }

headerFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
headerFontWeight w props = props { headerFontWeight = Just w }

dayHeaderFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
dayHeaderFontSize s props = props { dayHeaderFontSize = Just s }

dayHeaderFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
dayHeaderFontWeight w props = props { dayHeaderFontWeight = Just w }

dayFontSize :: forall msg. FontSize.FontSize -> CalendarProp msg
dayFontSize s props = props { dayFontSize = Just s }

dayFontWeight :: forall msg. FontWeight.FontWeight -> CalendarProp msg
dayFontWeight w props = props { dayFontWeight = Just w }

-- Behavior props

onSelect :: forall msg. (CalendarDate -> msg) -> CalendarProp msg
onSelect handler props = props { onSelect = Just handler }

onRangeSelect :: forall msg. (DateRange -> msg) -> CalendarProp msg
onRangeSelect handler props = props { onRangeSelect = Just handler }

onMultiSelect :: forall msg. (Array CalendarDate -> msg) -> CalendarProp msg
onMultiSelect handler props = props { onMultiSelect = Just handler }

onMonthChange :: forall msg. ({ year :: Int, month :: Int } -> msg) -> CalendarProp msg
onMonthChange handler props = props { onMonthChange = Just handler }

onPrevMonth :: forall msg. msg -> CalendarProp msg
onPrevMonth m props = props { onPrevMonth = Just m }

onNextMonth :: forall msg. msg -> CalendarProp msg
onNextMonth m props = props { onNextMonth = Just m }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // date operations
-- ═════════════════════════════════════════════════════════════════════════════

-- Pure Gregorian calendar arithmetic. No FFI. No JavaScript.

-- | Check if a year is a leap year
isLeapYear :: Int -> Boolean
isLeapYear year =
  (year `rem` 4 == 0 && year `rem` 100 /= 0) || year `rem` 400 == 0

-- | Get number of days in a month (1-indexed)
getDaysInMonth :: Int -> Int -> Int
getDaysInMonth year month = case month of
  1 -> 31
  2 -> if isLeapYear year then 29 else 28
  3 -> 31
  4 -> 30
  5 -> 31
  6 -> 30
  7 -> 31
  8 -> 31
  9 -> 30
  10 -> 31
  11 -> 30
  12 -> 31
  _ -> 0

-- | Day of week using Zeller's congruence (0 = Sunday, 6 = Saturday)
-- |
-- | Zeller's formula for Gregorian calendar:
-- |   h = (q + floor(13(m+1)/5) + K + floor(K/4) + floor(J/4) - 2J) mod 7
-- |
-- | January/February treated as months 13/14 of previous year.
dayOfWeek :: CalendarDate -> Int
dayOfWeek date =
  let
    adjustedYear = if date.month < 3 then date.year - 1 else date.year
    adjustedMonth = if date.month < 3 then date.month + 12 else date.month
    
    q = date.day
    m = adjustedMonth
    k = adjustedYear `rem` 100
    j = adjustedYear / 100
    
    h = (q + (13 * (m + 1)) / 5 + k + k / 4 + j / 4 - 2 * j) `rem` 7
    
    -- Zeller: 0=Saturday, 1=Sunday. Convert to 0=Sunday.
    dow = (h + 6) `rem` 7
  in
    if dow < 0 then dow + 7 else dow

-- | Get day of week for first day of month (0 = Sunday)
getFirstDayOfMonth :: Int -> Int -> Int
getFirstDayOfMonth year month = dayOfWeek { year, month, day: 1 }

-- | Compare two dates: -1 (a < b), 0 (equal), 1 (a > b)
compareDates :: CalendarDate -> CalendarDate -> Int
compareDates a b
  | a.year < b.year = -1
  | a.year > b.year = 1
  | a.month < b.month = -1
  | a.month > b.month = 1
  | a.day < b.day = -1
  | a.day > b.day = 1
  | otherwise = 0

-- | Check if two dates are the same
sameDate :: CalendarDate -> CalendarDate -> Boolean
sameDate a b = a.year == b.year && a.month == b.month && a.day == b.day

-- | Add days to a date (handles month/year overflow)
addDays :: CalendarDate -> Int -> CalendarDate
addDays date n
  | n == 0 = date
  | n > 0 = addDaysPositive date n
  | otherwise = addDaysNegative date (negate n)

-- | Add positive number of days
addDaysPositive :: CalendarDate -> Int -> CalendarDate
addDaysPositive date n =
  let
    daysInCurrentMonth = getDaysInMonth date.year date.month
    daysRemaining = daysInCurrentMonth - date.day
  in
    if n < daysRemaining + 1
      then date { day = date.day + n }
      else
        let
          nextMonth = if date.month == 12 then 1 else date.month + 1
          nextYear = if date.month == 12 then date.year + 1 else date.year
          nextDate = { year: nextYear, month: nextMonth, day: 1 }
          remaining = n - daysRemaining - 1
        in
          addDaysPositive nextDate remaining

-- | Subtract positive number of days
addDaysNegative :: CalendarDate -> Int -> CalendarDate
addDaysNegative date n =
  if n < date.day
    then date { day = date.day - n }
    else
      let
        prevMonth = if date.month == 1 then 12 else date.month - 1
        prevYear = if date.month == 1 then date.year - 1 else date.year
        daysInPrevMonth = getDaysInMonth prevYear prevMonth
        prevDate = { year: prevYear, month: prevMonth, day: daysInPrevMonth }
        remaining = n - date.day
      in
        addDaysNegative prevDate remaining

-- | Add months to a date (clamps day to valid range)
addMonths :: CalendarDate -> Int -> CalendarDate
addMonths date n =
  let
    totalMonths = date.year * 12 + (date.month - 1) + n
    newYear = totalMonths / 12
    newMonth = (totalMonths `rem` 12) + 1
    adjustedMonth = if newMonth < 1 then newMonth + 12 else newMonth
    adjustedYear = if newMonth < 1 then newYear - 1 else newYear
    maxDay = getDaysInMonth adjustedYear adjustedMonth
    newDay = if date.day > maxDay then maxDay else date.day
  in
    { year: adjustedYear, month: adjustedMonth, day: newDay }

-- | Get ISO 8601 week number (1-53)
-- |
-- | Week 1 contains the first Thursday of the year. Weeks start Monday.
getWeekNumber :: CalendarDate -> Int
getWeekNumber date =
  let
    dow = dayOfWeek date
    daysToThursday = (4 - dow + 7) `rem` 7
    thursday = addDays date daysToThursday
    jan1 = { year: thursday.year, month: 1, day: 1 }
    daysSinceJan1 = daysBetween jan1 thursday
  in
    daysSinceJan1 / 7 + 1

-- | Days between two dates (assumes b >= a)
daysBetween :: CalendarDate -> CalendarDate -> Int
daysBetween a b =
  let
    doyA = dayOfYear a
    doyB = dayOfYear b
  in
    if a.year == b.year
      then doyB - doyA
      else
        let
          daysRemainingInYearA = daysInYear a.year - doyA
          fullYears = countDaysInYears (a.year + 1) (b.year - 1)
        in
          daysRemainingInYearA + fullYears + doyB

-- | Day of year (1-365 or 1-366)
dayOfYear :: CalendarDate -> Int
dayOfYear date = go 1 0
  where
  go :: Int -> Int -> Int
  go m acc
    | m == date.month = acc + date.day
    | otherwise = go (m + 1) (acc + getDaysInMonth date.year m)

-- | Total days in a year
daysInYear :: Int -> Int
daysInYear year = if isLeapYear year then 366 else 365

-- | Sum days in range of years (inclusive)
countDaysInYears :: Int -> Int -> Int
countDaysInYears startYear endYear
  | startYear > endYear = 0
  | otherwise = daysInYear startYear + countDaysInYears (startYear + 1) endYear

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // month grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build the month grid for a given year/month
buildMonthGrid :: Int -> Int -> WeekStart -> MonthGrid
buildMonthGrid year month weekStart =
  let
    daysInMonth = getDaysInMonth year month
    firstDayOfWeek = getFirstDayOfMonth year month
    startOffset = weekStartIndex weekStart
    
    -- Adjust first day based on week start
    adjustedFirstDay = (firstDayOfWeek - startOffset + 7) `rem` 7
    
    -- Build all day cells
    allDays = buildDayCells year month daysInMonth adjustedFirstDay
    
    -- Split into weeks
    weeks = splitIntoWeeks allDays year month
  in
    { year, month, weeks }

-- | Build day cells with padding
buildDayCells :: Int -> Int -> Int -> Int -> Array MonthDay
buildDayCells year month daysInMonth offset =
  let
    -- Leading empty cells
    leadingEmpty = buildEmptyCells offset
    
    -- Actual day cells
    dayCells = buildDateCells year month daysInMonth
    
    -- Trailing empty cells to complete last week
    totalCells = offset + daysInMonth
    trailingCount = (7 - (totalCells `rem` 7)) `rem` 7
    trailingEmpty = buildEmptyCells trailingCount
  in
    leadingEmpty <> dayCells <> trailingEmpty

-- | Build empty cells
buildEmptyCells :: Int -> Array MonthDay
buildEmptyCells count = go count []
  where
  go :: Int -> Array MonthDay -> Array MonthDay
  go n acc
    | n < 1 = acc
    | otherwise = go (n - 1) (acc `snoc` DayEmpty)

-- | Build date cells
buildDateCells :: Int -> Int -> Int -> Array MonthDay
buildDateCells year month daysInMonth = go 1 []
  where
  go :: Int -> Array MonthDay -> Array MonthDay
  go day acc
    | day > daysInMonth = acc
    | otherwise = go (day + 1) (acc `snoc` DayDate { year, month, day })

-- | Split day cells into weeks
splitIntoWeeks :: Array MonthDay -> Int -> Int -> Array MonthWeek
splitIntoWeeks days _year _month = go 0 days []
  where
  go :: Int -> Array MonthDay -> Array MonthWeek -> Array MonthWeek
  go _ [] acc = acc
  go weekIdx remaining acc =
    let
      week = Array.take 7 remaining
      rest = Array.drop 7 remaining
      -- Calculate week number from first non-empty day
      weekNum = case Array.findMap getDateFromDay week of
        Just d -> getWeekNumber d
        Nothing -> weekIdx + 1
    in
      go (weekIdx + 1) rest (acc `snoc` { weekNumber: weekNum, days: week })
  
  getDateFromDay :: MonthDay -> Maybe CalendarDate
  getDateFromDay (DayDate d) = Just d
  getDateFromDay DayEmpty = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a calendar
calendar :: forall msg. Array (CalendarProp msg) -> E.Element msg
calendar propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    renderCalendarContainer props
      [ renderHeader props
      , renderDayHeaders props
      , renderWeeks props grid
      ]

-- | Render calendar with navigation controls
calendarWithNav :: forall msg. Array (CalendarProp msg) -> E.Element msg
calendarWithNav propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    grid = buildMonthGrid props.viewYear props.viewMonth props.weekStartsOn
  in
    renderCalendarContainer props
      [ renderNavHeader props
      , renderDayHeaders props
      , renderWeeks props grid
      ]

-- | Render the calendar container
renderCalendarContainer :: forall msg. CalendarProps msg -> Array (E.Element msg) -> E.Element msg
renderCalendarContainer props children =
  let
    bgStyle = maybe "" Color.toLegacyCss props.backgroundColor
    brdrColor = maybe "" Color.toLegacyCss props.borderColor
    radiusStyle = maybe "" Geometry.toLegacyCss props.borderRadius
    padStyle = maybe "" show props.padding
    brdrWidth = maybe "" show props.borderWidth
  in
    E.div_
      ( [ E.attr "role" "grid"
        , E.attr "aria-label" "Calendar"
        , E.style "display" "flex"
        , E.style "flex-direction" "column"
        ] <> maybeStyle "background-color" bgStyle
          <> maybeStyle "border-color" brdrColor
          <> maybeStyle "border-radius" radiusStyle
          <> maybeStyle "padding" padStyle
          <> maybeStyle "border-width" brdrWidth
          <> (if brdrWidth == "" then [] else [ E.style "border-style" "solid" ])
      )
      children

-- | Render the month/year header (without navigation)
renderHeader :: forall msg. CalendarProps msg -> E.Element msg
renderHeader props =
  let
    hdrColor = maybe "" Color.toLegacyCss props.headerColor
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "justify-content" "center"
        , E.style "padding-top" "4px"
        , E.style "align-items" "center"
        ] <> maybeStyle "color" hdrColor
      )
      [ E.div_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          ]
          [ E.text (monthName EnUS props.viewMonth <> " " <> show props.viewYear) ]
      ]

-- | Render navigation header with prev/next buttons
renderNavHeader :: forall msg. CalendarProps msg -> E.Element msg
renderNavHeader props =
  let
    hdrColor = maybe "" Color.toLegacyCss props.headerColor
    navColor = maybe "" Color.toLegacyCss props.navButtonColor
    navRadius = maybe "" Geometry.toLegacyCss props.navButtonRadius
    cSize = maybe "36px" show props.cellSize
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "justify-content" "space-between"
        , E.style "align-items" "center"
        , E.style "padding" "4px 8px 8px 8px"
        ] <> maybeStyle "color" hdrColor
      )
      [ -- Previous month button
        renderNavButton props.onPrevMonth navColor navRadius cSize (E.text "\x2039")
      , -- Month/Year display
        E.div_
          [ E.style "font-size" "14px"
          , E.style "font-weight" "500"
          ]
          [ E.text (monthName EnUS props.viewMonth <> " " <> show props.viewYear) ]
      , -- Next month button
        renderNavButton props.onNextMonth navColor navRadius cSize (E.text "\x203a")
      ]

-- | Render a navigation button
renderNavButton :: forall msg. Maybe msg -> String -> String -> String -> E.Element msg -> E.Element msg
renderNavButton handler colorStyle radiusStyle sizeStyle content =
  E.button_
    ( [ E.attr "type" "button"
      , E.style "width" sizeStyle
      , E.style "height" sizeStyle
      , E.style "background" "transparent"
      , E.style "border" "none"
      , E.style "cursor" "pointer"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "font-size" "18px"
      ] <> maybeStyle "color" colorStyle
        <> maybeStyle "border-radius" radiusStyle
        <> case handler of
             Just msg -> [ E.onClick msg ]
             Nothing -> [ E.attr "disabled" "true" ]
    )
    [ content ]

-- | Render day-of-week headers
renderDayHeaders :: forall msg. CalendarProps msg -> E.Element msg
renderDayHeaders props =
  let
    baseDays = ["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"]
    days = case props.weekStartsOn of
      Sunday -> baseDays
      Monday -> rotateArray 1 baseDays
    dayHdrColor = maybe "" Color.toLegacyCss props.dayHeaderColor
    cSize = maybe "36px" show props.cellSize
  in
    E.div_
      [ E.attr "role" "row"
      , E.style "display" "flex"
      ]
      ( (if props.showWeekNumbers then [ renderWeekNumHeader dayHdrColor cSize ] else [])
        <> map (renderDayHeader dayHdrColor cSize) days
      )

-- | Render week number column header
renderWeekNumHeader :: forall msg. String -> String -> E.Element msg
renderWeekNumHeader colorStyle sizeStyle =
  E.div_
    ( [ E.style "width" sizeStyle
      , E.style "font-size" "12px"
      , E.style "text-align" "center"
      , E.style "font-weight" "400"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      ] <> maybeStyle "color" colorStyle
    )
    [ E.text "#" ]

-- | Render a day header
renderDayHeader :: forall msg. String -> String -> String -> E.Element msg
renderDayHeader colorStyle sizeStyle day =
  E.div_
    ( [ E.attr "role" "columnheader"
      , E.style "width" sizeStyle
      , E.style "font-size" "12px"
      , E.style "text-align" "center"
      , E.style "font-weight" "400"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      ] <> maybeStyle "color" colorStyle
    )
    [ E.text day ]

-- | Render all weeks
renderWeeks :: forall msg. CalendarProps msg -> MonthGrid -> E.Element msg
renderWeeks props grid =
  let
    gapStyle = maybe "" show props.gap
  in
    E.div_
      ( [ E.style "display" "flex"
        , E.style "flex-direction" "column"
        ] <> maybeStyle "gap" gapStyle
      )
      (map (renderWeek props) grid.weeks)

-- | Render a single week
renderWeek :: forall msg. CalendarProps msg -> MonthWeek -> E.Element msg
renderWeek props week =
  E.div_
    [ E.attr "role" "row"
    , E.style "display" "flex"
    ]
    ( (if props.showWeekNumbers then [ renderWeekNumber props week.weekNumber ] else [])
      <> map (renderDay props) week.days
    )

-- | Render week number
renderWeekNumber :: forall msg. CalendarProps msg -> Int -> E.Element msg
renderWeekNumber props num =
  let
    cSize = maybe "36px" show props.cellSize
    dayHdrColor = maybe "" Color.toLegacyCss props.dayHeaderColor
  in
    E.div_
      ( [ E.style "width" cSize
        , E.style "font-size" "12px"
        , E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        ] <> maybeStyle "color" dayHdrColor
      )
      [ E.text (show num) ]

-- | Render a single day cell
renderDay :: forall msg. CalendarProps msg -> MonthDay -> E.Element msg
renderDay props day = case day of
  DayEmpty -> renderEmptyCell props
  DayDate date -> renderDateCell props date

-- | Render an empty day cell
renderEmptyCell :: forall msg. CalendarProps msg -> E.Element msg
renderEmptyCell props =
  let
    cSize = maybe "36px" show props.cellSize
  in
    E.div_
      [ E.style "width" cSize
      , E.style "height" cSize
      ]
      []

-- | Render a date cell
renderDateCell :: forall msg. CalendarProps msg -> CalendarDate -> E.Element msg
renderDateCell props date =
  let
    isDisabled = isDateDisabledProp props date
    isSelected = isDateSelected props date
    isInRange = isDateInSelectedRange props date
    isRangeStartDate = isDateRangeStart props date
    isRangeEndDate = isDateRangeEnd props date
    
    cSize = maybe "36px" show props.cellSize
    cellRadius = maybe "" Geometry.toLegacyCss props.dayCellRadius
    
    -- Determine colors based on state
    bgColor
      | isSelected = maybe "" Color.toLegacyCss props.selectedColor
      | isInRange = maybe "" Color.toLegacyCss props.rangeColor
      | otherwise = ""
    
    txtColor
      | isDisabled = maybe "" Color.toLegacyCss props.disabledColor
      | isSelected = maybe "" Color.toLegacyCss props.selectedTextColor
      | otherwise = maybe "" Color.toLegacyCss props.textColor
    
    -- Border radius adjustments for range
    radiusStyle
      | isRangeStartDate && isRangeEndDate = cellRadius
      | isRangeStartDate = cellRadius <> " 0 0 " <> cellRadius
      | isRangeEndDate = "0 " <> cellRadius <> " " <> cellRadius <> " 0"
      | isInRange = "0"
      | otherwise = cellRadius
    
    cursorStyle
      | isDisabled = "not-allowed"
      | otherwise = "pointer"
    
    opacityStyle
      | isDisabled = "0.5"
      | otherwise = "1"
  in
    E.button_
      ( [ E.attr "type" "button"
        , E.attr "role" "gridcell"
        , E.style "width" cSize
        , E.style "height" cSize
        , E.style "border" "none"
        , E.style "font-size" "14px"
        , E.style "display" "inline-flex"
        , E.style "align-items" "center"
        , E.style "justify-content" "center"
        , E.style "cursor" cursorStyle
        , E.style "opacity" opacityStyle
        ] <> maybeStyle "background-color" bgColor
          <> maybeStyle "color" txtColor
          <> maybeStyle "border-radius" radiusStyle
          <> (if isDisabled then [ E.attr "disabled" "true" ] else [])
          <> (if isDisabled then [] else
                case props.onSelect of
                  Just handler -> [ E.onClick (handler date) ]
                  Nothing -> [])
      )
      [ E.text (show date.day) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a date is within a range (inclusive)
isDateInRange :: CalendarDate -> Maybe CalendarDate -> Maybe CalendarDate -> Boolean
isDateInRange date minD maxD =
  let
    afterMin = case minD of
      Nothing -> true
      Just minVal -> compareDates date minVal >= 0
    beforeMax = case maxD of
      Nothing -> true
      Just maxVal -> compareDates date maxVal < 1
  in afterMin && beforeMax

-- | Check if date is disabled based on props
isDateDisabledProp :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateDisabledProp props date =
  props.disabledDates date || not (isDateInRange date props.minDate props.maxDate)

-- | Check if date is selected
isDateSelected :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateSelected props date = case props.selectionMode of
  Single -> case props.selected of
    Just sel -> sameDate date sel
    Nothing -> false
  Range ->
    (case props.rangeStart of
      Just start -> sameDate date start
      Nothing -> false)
    ||
    (case props.rangeEnd of
      Just end -> sameDate date end
      Nothing -> false)
  Multiple -> Array.any (sameDate date) props.multiSelected

-- | Check if date is within selected range
isDateInSelectedRange :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateInSelectedRange props date = case props.selectionMode of
  Range -> case props.rangeStart, props.rangeEnd of
    Just start, Just end ->
      compareDates date start >= 0 && compareDates date end < 1
    _, _ -> false
  _ -> false

-- | Check if date is range start
isDateRangeStart :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateRangeStart props date = case props.rangeStart of
  Just start -> sameDate date start
  Nothing -> false

-- | Check if date is range end
isDateRangeEnd :: forall msg. CalendarProps msg -> CalendarDate -> Boolean
isDateRangeEnd props date = case props.rangeEnd of
  Just end -> sameDate date end
  Nothing -> false

-- | Month name lookup by locale
monthName :: Locale -> Int -> String
monthName locale month = case locale of
  EnUS -> monthNameEnUS month
  EnGB -> monthNameEnUS month  -- Same as US English
  De -> monthNameDe month
  Fr -> monthNameFr month
  Es -> monthNameEs month
  Ja -> monthNameJa month
  Zh -> monthNameZh month

-- | English month names
monthNameEnUS :: Int -> String
monthNameEnUS = case _ of
  1 -> "January"
  2 -> "February"
  3 -> "March"
  4 -> "April"
  5 -> "May"
  6 -> "June"
  7 -> "July"
  8 -> "August"
  9 -> "September"
  10 -> "October"
  11 -> "November"
  12 -> "December"
  _ -> "Unknown"

-- | German month names
monthNameDe :: Int -> String
monthNameDe = case _ of
  1 -> "Januar"
  2 -> "Februar"
  3 -> "März"
  4 -> "April"
  5 -> "Mai"
  6 -> "Juni"
  7 -> "Juli"
  8 -> "August"
  9 -> "September"
  10 -> "Oktober"
  11 -> "November"
  12 -> "Dezember"
  _ -> "Unbekannt"

-- | French month names
monthNameFr :: Int -> String
monthNameFr = case _ of
  1 -> "janvier"
  2 -> "février"
  3 -> "mars"
  4 -> "avril"
  5 -> "mai"
  6 -> "juin"
  7 -> "juillet"
  8 -> "août"
  9 -> "septembre"
  10 -> "octobre"
  11 -> "novembre"
  12 -> "décembre"
  _ -> "inconnu"

-- | Spanish month names
monthNameEs :: Int -> String
monthNameEs = case _ of
  1 -> "enero"
  2 -> "febrero"
  3 -> "marzo"
  4 -> "abril"
  5 -> "mayo"
  6 -> "junio"
  7 -> "julio"
  8 -> "agosto"
  9 -> "septiembre"
  10 -> "octubre"
  11 -> "noviembre"
  12 -> "diciembre"
  _ -> "desconocido"

-- | Japanese month names
monthNameJa :: Int -> String
monthNameJa = case _ of
  1 -> "1月"
  2 -> "2月"
  3 -> "3月"
  4 -> "4月"
  5 -> "5月"
  6 -> "6月"
  7 -> "7月"
  8 -> "8月"
  9 -> "9月"
  10 -> "10月"
  11 -> "11月"
  12 -> "12月"
  _ -> "不明"

-- | Chinese month names
monthNameZh :: Int -> String
monthNameZh = case _ of
  1 -> "一月"
  2 -> "二月"
  3 -> "三月"
  4 -> "四月"
  5 -> "五月"
  6 -> "六月"
  7 -> "七月"
  8 -> "八月"
  9 -> "九月"
  10 -> "十月"
  11 -> "十一月"
  12 -> "十二月"
  _ -> "未知"

-- | Rotate an array by n positions
rotateArray :: forall a. Int -> Array a -> Array a
rotateArray n arr = Array.drop n arr <> Array.take n arr

-- | Helper to add style only if value is non-empty
maybeStyle :: forall msg. String -> String -> Array (E.Attribute msg)
maybeStyle _ "" = []
maybeStyle prop val = [ E.style prop val ]
