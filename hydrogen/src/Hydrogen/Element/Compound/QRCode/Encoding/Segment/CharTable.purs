-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // element // qrcode // encoding // segment // chartable
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Character lookup tables for QR encoding modes.

module Hydrogen.Element.Compound.QRCode.Encoding.Segment.CharTable
  ( alphanumericValue
  , isAlphanumericChar
  , isNumericChar
  , charToString
  ) where

import Prelude
  ( otherwise
  , (&&)
  , (||)
  , (-)
  , (>=)
  , (<=)
  , (<)
  , (==)
  , (<>)
  )

import Data.Char (toCharCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // alphanumeric table
-- ═════════════════════════════════════════════════════════════════════════════

alphanumericValue :: Char -> Int
alphanumericValue c =
  let code = toCharCode c
  in
    if code >= 48 && code <= 57 then code - 48
    else if code >= 65 && code <= 90 then code - 55
    else case code of
      32 -> 36
      36 -> 37
      37 -> 38
      42 -> 39
      43 -> 40
      45 -> 41
      46 -> 42
      47 -> 43
      58 -> 44
      _ -> 0

isAlphanumericChar :: Char -> Boolean
isAlphanumericChar c =
  let code = toCharCode c
  in
    (code >= 48 && code <= 57) ||
    (code >= 65 && code <= 90) ||
    code == 32 ||
    code == 36 ||
    code == 37 ||
    code == 42 ||
    code == 43 ||
    code == 45 ||
    code == 46 ||
    code == 47 ||
    code == 58

isNumericChar :: Char -> Boolean
isNumericChar c =
  let code = toCharCode c
  in code >= 48 && code <= 57

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // char to string
-- ═════════════════════════════════════════════════════════════════════════════

charToString :: Char -> String
charToString c =
  let code = toCharCode c
  in if code < 128 then asciiToString code else "?"

asciiToString :: Int -> String
asciiToString code
  | code >= 48 && code <= 57 = digitString (code - 48)
  | code >= 65 && code <= 90 = upperString (code - 65)
  | code >= 97 && code <= 122 = lowerString (code - 97)
  | code == 32 = " "
  | code == 36 = "$"
  | code == 37 = "%"
  | code == 42 = "*"
  | code == 43 = "+"
  | code == 45 = "-"
  | code == 46 = "."
  | code == 47 = "/"
  | code == 58 = ":"
  | code == 33 = "!"
  | code == 34 = "\""
  | code == 35 = "#"
  | code == 38 = "&"
  | code == 39 = "'"
  | code == 40 = "("
  | code == 41 = ")"
  | code == 44 = ","
  | code == 59 = ";"
  | code == 60 = "<"
  | code == 61 = "="
  | code == 62 = ">"
  | code == 63 = "?"
  | code == 64 = "@"
  | code == 91 = "["
  | code == 92 = "\\"
  | code == 93 = "]"
  | code == 94 = "^"
  | code == 95 = "_"
  | code == 96 = "`"
  | code == 123 = "{"
  | code == 124 = "|"
  | code == 125 = "}"
  | code == 126 = "~"
  | code == 10 = "\n"
  | code == 13 = "\r"
  | code == 9 = "\t"
  | otherwise = "?"

digitString :: Int -> String
digitString n = case n of
  0 -> "0"
  1 -> "1"
  2 -> "2"
  3 -> "3"
  4 -> "4"
  5 -> "5"
  6 -> "6"
  7 -> "7"
  8 -> "8"
  9 -> "9"
  _ -> "?"

upperString :: Int -> String
upperString n = case n of
  0 -> "A"
  1 -> "B"
  2 -> "C"
  3 -> "D"
  4 -> "E"
  5 -> "F"
  6 -> "G"
  7 -> "H"
  8 -> "I"
  9 -> "J"
  10 -> "K"
  11 -> "L"
  12 -> "M"
  13 -> "N"
  14 -> "O"
  15 -> "P"
  16 -> "Q"
  17 -> "R"
  18 -> "S"
  19 -> "T"
  20 -> "U"
  21 -> "V"
  22 -> "W"
  23 -> "X"
  24 -> "Y"
  25 -> "Z"
  _ -> "?"

lowerString :: Int -> String
lowerString n = case n of
  0 -> "a"
  1 -> "b"
  2 -> "c"
  3 -> "d"
  4 -> "e"
  5 -> "f"
  6 -> "g"
  7 -> "h"
  8 -> "i"
  9 -> "j"
  10 -> "k"
  11 -> "l"
  12 -> "m"
  13 -> "n"
  14 -> "o"
  15 -> "p"
  16 -> "q"
  17 -> "r"
  18 -> "s"
  19 -> "t"
  20 -> "u"
  21 -> "v"
  22 -> "w"
  23 -> "x"
  24 -> "y"
  25 -> "z"
  _ -> "?"
