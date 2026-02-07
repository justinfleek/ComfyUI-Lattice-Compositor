-- |
-- Module      : Lattice.Services.SVGPathParsing
-- Description : Pure SVG path parsing functions
-- 
-- Migrated from src/lattice/nodes/lattice_vectorize.py
-- Pure functions for parsing SVG path data into control points
-- Handles all SVG path commands: M, L, H, V, C, S, Q, T, A, Z
--

module Lattice.Services.SVGPathParsing
  ( -- Types
    ControlPoint(..)
  , ControlPointHandle(..)
  , ControlPointType(..)
  , ParsedPath(..)
  -- Parsing functions
  , parseSVGToPaths
  , parsePathData
  ) where

import Data.Char (isDigit, toUpper, isSpace)
import Lattice.Utils.NumericSafety (isFinite)
import Data.List (findIndices, findIndex, tails)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Text.Read (readMaybe)

import Lattice.Utils.NumericSafety
  ( clamp01
  , safeLerp
  )

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Control point handle (bezier control point relative to main point)
data ControlPointHandle = ControlPointHandle
  { controlPointHandleX :: Double
  , controlPointHandleY :: Double
  } deriving (Eq, Show)

-- | Control point type (corner or smooth)
data ControlPointType = CornerPoint | SmoothPoint deriving (Eq, Show)

-- | A control point in a path
data ControlPoint = ControlPoint
  { controlPointId :: Text
  , controlPointX :: Double
  , controlPointY :: Double
  , controlPointInHandle :: Maybe ControlPointHandle
  , controlPointOutHandle :: Maybe ControlPointHandle
  , controlPointType :: ControlPointType
  } deriving (Eq, Show)

-- | A parsed path with metadata
data ParsedPath = ParsedPath
  { parsedPathId :: Text
  , parsedPathFill :: Text
  , parsedPathStroke :: Text
  , parsedPathControlPoints :: [ControlPoint]
  , parsedPathClosed :: Bool
  } deriving (Eq, Show)

-- ============================================================================
-- SVG PATH PARSING
-- ============================================================================

-- | Parse SVG string and extract paths with control points
--
-- Converts SVG path commands to ControlPoint format:
-- - M = moveTo (start new path)
-- - L = lineTo (straight line)
-- - C = cubic bezier (with two control points)
-- - Q = quadratic bezier (one control point, convert to cubic)
-- - Z = closePath
--
-- Returns list of path objects with controlPoints arrays.
parseSVGToPaths :: Text -> Int -> Int -> [ParsedPath]
parseSVGToPaths svgString imgWidth imgHeight =
  let
    -- Manual SVG parsing: find all <path> elements
    svgStr = T.unpack svgString
    
    -- Find all path element start positions
    findPathElements :: String -> [String]
    findPathElements s =
      let
        findNext idx =
          let
            remaining = drop idx s
            pathStart = "<path"
            pathEnd = "/>"
            pathEnd2 = "</path>"
          in
            case remaining of
              [] -> []
              _ ->
                case dropWhile (not . isPrefixOf pathStart) (tails remaining) of
                  [] -> []
                  pathRem : _ ->
                    let
                      -- Find end of path tag
                      findEnd tagEnd = case findIndex (isPrefixOf tagEnd) (tails pathRem) of
                        Just endIdx -> Just (take (endIdx + length tagEnd) pathRem)
                        Nothing -> Nothing
                      
                      pathTag = case findEnd pathEnd of
                        Just tag -> Just tag
                        Nothing -> findEnd pathEnd2
                    in
                      case pathTag of
                        Just tag -> tag : findNext (idx + length remaining - length pathRem + length tag)
                        Nothing -> []
      in
        findNext 0
    
    isPrefixOf :: String -> String -> Bool
    isPrefixOf [] _ = True
    isPrefixOf _ [] = False
    isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys
    
    -- Extract attribute value from attribute string
    extractAttr :: String -> String -> Maybe String
    extractAttr attrName attrsStr =
      let
        attrPattern = attrName ++ "=\""
        attrPattern2 = attrName ++ "='"
      in
        case findIndex (isPrefixOf attrPattern) (tails attrsStr) of
          Just idx ->
            let
              afterQuote = drop (idx + length attrPattern) attrsStr
              endIdx = case findIndex (== '"') afterQuote of
                Just e -> e
                Nothing -> length afterQuote
            in
              Just (take endIdx afterQuote)
          Nothing ->
            case findIndex (isPrefixOf attrPattern2) (tails attrsStr) of
              Just idx ->
                let
                  afterQuote = drop (idx + length attrPattern2) attrsStr
                  endIdx = case findIndex (== '\'') afterQuote of
                    Just e -> e
                    Nothing -> length afterQuote
                in
                  Just (take endIdx afterQuote)
              Nothing -> Nothing
    
    
    -- Process each path element
    processPath idx pathTag =
      let
        -- Extract attributes (everything between <path and /> or >)
        attrsStart = case findIndex (== ' ') pathTag of
          Just idx' -> drop (idx' + 1) pathTag
          Nothing -> ""
        attrsStr = case findIndex (== '>') attrsStart of
          Just idx' -> take idx' attrsStart
          Nothing -> attrsStart
        
        -- Extract d, fill, stroke attributes
        pathData = extractAttr "d" attrsStr
        fill = fromMaybe "" (extractAttr "fill" attrsStr)
        stroke = fromMaybe "" (extractAttr "stroke" attrsStr)
        
        -- Skip invisible paths
        isVisible = fill /= "none" && (null stroke || stroke /= "none")
      in
        case pathData of
          Nothing -> Nothing
          Just d ->
            if not isVisible
              then Nothing
              else
                let
                  (controlPoints, isClosed) = parsePathData (T.pack d) idx
                in
                  if length controlPoints < 2
                    then Nothing
                    else Just $ ParsedPath
                      { parsedPathId = T.pack ("path_" ++ show idx)
                      , parsedPathFill = if fill == "none" then T.empty else T.pack fill
                      , parsedPathStroke = if stroke == "none" then T.empty else T.pack stroke
                      , parsedPathControlPoints = controlPoints
                      , parsedPathClosed = isClosed
                      }
    
    pathElements = findPathElements svgStr
    paths = zipWith processPath [0..] pathElements
    validPaths = [p | Just p <- paths]
  in
    validPaths

-- | Parse SVG path data string into control points
--
-- Handles:
-- - M/m: moveTo (absolute/relative)
-- - L/l: lineTo
-- - H/h: horizontal line
-- - V/v: vertical line
-- - C/c: cubic bezier
-- - S/s: smooth cubic bezier
-- - Q/q: quadratic bezier
-- - T/t: smooth quadratic bezier
-- - A/a: arc (approximated as line)
-- - Z/z: close path
--
-- Returns (control_points, is_closed)
parsePathData :: Text -> Int -> ([ControlPoint], Bool)
parsePathData d pathIdx =
  let
    -- Manual tokenizer: parse commands and numbers from path string
    pathStr = T.unpack d
    
    -- Check if character is a command letter
    isCommandChar :: Char -> Bool
    isCommandChar c = c `elem` "MmLlHhVvCcSsQqTtAaZz"
    
    -- Parse a number from string, returning (number, remaining_string)
    parseNumber :: String -> Maybe (Double, String)
    parseNumber s =
      let
        -- Skip whitespace and commas
        skipWhitespace = dropWhile (\c -> isSpace c || c == ',')
        s' = skipWhitespace s
        
        -- Find the end of the number
        -- Number can start with + or -, then digits, optional decimal point, more digits, optional exponent
        findNumberEnd [] = 0
        findNumberEnd (c:cs)
          | c == '+' || c == '-' = 1 + findNumberEnd cs
          | isDigit c = 1 + findNumberEnd cs
          | c == '.' = 1 + findNumberEnd cs
          | c == 'e' || c == 'E' = 1 + findNumberEnd cs
          | otherwise = 0
        
        numEnd = findNumberEnd s'
        numStr = take numEnd s'
        rest = drop numEnd s'
      in
        if null numStr
          then Nothing
          else case readMaybe numStr of
            Just num -> Just (num, rest)
            Nothing -> Nothing
    
    -- Tokenize: extract commands and numbers
    tokenize :: String -> [(Maybe Char, [Double])]
    tokenize [] = []
    tokenize s =
      let
        s' = dropWhile (\c -> isSpace c || c == ',') s
      in
        case s' of
          [] -> []
          (firstChar:rest) ->
            if isCommandChar firstChar
              then
                -- Found a command, collect its arguments
                let
                  cmd = Just firstChar
                  (args, nextRest) = collectArgs rest []
                in
                  (cmd, reverse args) : tokenize nextRest
              else
                -- No command found, skip (shouldn't happen in valid SVG)
                tokenize rest
    
    -- Collect arguments for current command
    collectArgs :: String -> [Double] -> ([Double], String)
    collectArgs s acc =
      let
        s' = dropWhile (\c -> isSpace c || c == ',') s
      in
        case s' of
          [] -> (acc, s')
          (firstChar:_) ->
            if isCommandChar firstChar
              then (acc, s')
              else
                case parseNumber s' of
                  Just (num, rest) -> collectArgs rest (num : acc)
                  Nothing -> (acc, s')
    
    commands = tokenize pathStr
    
    -- Process commands
    processCommands cmds =
      let
        initialState = PathState
          { pathStatePathIdx = pathIdx
          , pathStateCurrentX = 0.0
          , pathStateCurrentY = 0.0
          , pathStateStartX = 0.0
          , pathStateStartY = 0.0
          , pathStateLastCpX = Nothing
          , pathStateLastCpY = Nothing
          , pathStatePoints = []
          , pathStatePointIdx = 0
          , pathStateClosed = False
          }
        
        finalState = foldl processCommand initialState cmds
      in
        (reverse (pathStatePoints finalState), pathStateClosed finalState)
    
    processCommand state (Nothing, _) = state
    processCommand state (Just cmd, args) =
      let
        isRelative = cmd `elem` "mlhvcsqtaz"
        cmdUpper = toUpper cmd
      in
        case cmdUpper of
          'M' -> processMoveTo state isRelative args
          'L' -> processLineTo state isRelative args
          'H' -> processHorizontalLine state isRelative args
          'V' -> processVerticalLine state isRelative args
          'C' -> processCubicBezier state isRelative args
          'S' -> processSmoothCubic state isRelative args
          'Q' -> processQuadraticBezier state isRelative args
          'T' -> processSmoothQuadratic state isRelative args
          'A' -> processArc state isRelative args
          'Z' -> processClosePath state
          _ -> state
  in
    processCommands commands

-- ============================================================================
-- INTERNAL STATE
-- ============================================================================

data PathState = PathState
  { pathStatePathIdx :: Int  -- Path index for ID generation
  , pathStateCurrentX :: Double
  , pathStateCurrentY :: Double
  , pathStateStartX :: Double
  , pathStateStartY :: Double
  , pathStateLastCpX :: Maybe Double
  , pathStateLastCpY :: Maybe Double
  , pathStatePoints :: [ControlPoint]
  , pathStatePointIdx :: Int
  , pathStateClosed :: Bool
  } deriving (Eq, Show)

-- ============================================================================
-- COMMAND PROCESSORS
-- ============================================================================

processMoveTo :: PathState -> Bool -> [Double] -> PathState
processMoveTo state isRelative args =
  let
    processCoords [] s = s
    processCoords (x:y:rest) s =
      let
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Nothing
          , controlPointOutHandle = Nothing
          , controlPointType = CornerPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStateStartX = if pathStatePointIdx s == 0 then absX else pathStateStartX s
          , pathStateStartY = if pathStatePointIdx s == 0 then absY else pathStateStartY s
          , pathStatePoints = newPoint : pathStatePoints s
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Nothing
          , pathStateLastCpY = Nothing
          }
      in
        processCoords rest newState
    processCoords _ s = s
  in
    processCoords args state

processLineTo :: PathState -> Bool -> [Double] -> PathState
processLineTo state isRelative args =
  let
    processCoords [] s = s
    processCoords (x:y:rest) s =
      let
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Nothing
          , controlPointOutHandle = Nothing
          , controlPointType = CornerPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : pathStatePoints s
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Nothing
          , pathStateLastCpY = Nothing
          }
      in
        processCoords rest newState
    processCoords _ s = s
  in
    processCoords args state

processHorizontalLine :: PathState -> Bool -> [Double] -> PathState
processHorizontalLine state isRelative args =
  let
    processX [] s = s
    processX (x:rest) s =
      let
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = pathStateCurrentY s
          , controlPointInHandle = Nothing
          , controlPointOutHandle = Nothing
          , controlPointType = CornerPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStatePoints = newPoint : pathStatePoints s
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Nothing
          , pathStateLastCpY = Nothing
          }
      in
        processX rest newState
  in
    processX args state

processVerticalLine :: PathState -> Bool -> [Double] -> PathState
processVerticalLine state isRelative args =
  let
    processY [] s = s
    processY (y:rest) s =
      let
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = pathStateCurrentX s
          , controlPointY = absY
          , controlPointInHandle = Nothing
          , controlPointOutHandle = Nothing
          , controlPointType = CornerPoint
          }
        
        newState = s
          { pathStateCurrentX = pathStateCurrentX s
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : pathStatePoints s
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Nothing
          , pathStateLastCpY = Nothing
          }
      in
        processY rest newState
  in
    processY args state

processCubicBezier :: PathState -> Bool -> [Double] -> PathState
processCubicBezier state isRelative args =
  let
    processBezier [] s = s
    processBezier (cp1x:cp1y:cp2x:cp2y:x:y:rest) s =
      let
        absCp1x = cp1x + (if isRelative then pathStateCurrentX s else 0.0)
        absCp1y = cp1y + (if isRelative then pathStateCurrentY s else 0.0)
        absCp2x = cp2x + (if isRelative then pathStateCurrentX s else 0.0)
        absCp2y = cp2y + (if isRelative then pathStateCurrentY s else 0.0)
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        -- Update previous point's handleOut
        updatedPoints = case pathStatePoints s of
          [] -> []
          (p:ps) ->
            let
              updatedP = p
                { controlPointOutHandle = Just (ControlPointHandle absCp1x absCp1y)
                , controlPointType = if controlPointInHandle p == Nothing
                  then CornerPoint
                  else SmoothPoint
                }
            in
              updatedP : ps
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Just (ControlPointHandle absCp2x absCp2y)
          , controlPointOutHandle = Nothing
          , controlPointType = SmoothPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : updatedPoints
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Just absCp2x
          , pathStateLastCpY = Just absCp2y
          }
      in
        processBezier rest newState
    processBezier _ s = s
  in
    processBezier args state

processSmoothCubic :: PathState -> Bool -> [Double] -> PathState
processSmoothCubic state isRelative args =
  let
    processSmooth [] s = s
    processSmooth (cp2x:cp2y:x:y:rest) s =
      let
        -- Reflect last control point
        (cp1x, cp1y) = case (pathStateLastCpX s, pathStateLastCpY s) of
          (Just lx, Just ly) -> (2 * pathStateCurrentX s - lx, 2 * pathStateCurrentY s - ly)
          _ -> (pathStateCurrentX s, pathStateCurrentY s)
        
        absCp2x = cp2x + (if isRelative then pathStateCurrentX s else 0.0)
        absCp2y = cp2y + (if isRelative then pathStateCurrentY s else 0.0)
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        -- Update previous point's handleOut
        updatedPoints = case pathStatePoints s of
          [] -> []
          (p:ps) ->
            let
              updatedP = p
                { controlPointOutHandle = Just (ControlPointHandle cp1x cp1y)
                , controlPointType = SmoothPoint
                }
            in
              updatedP : ps
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Just (ControlPointHandle absCp2x absCp2y)
          , controlPointOutHandle = Nothing
          , controlPointType = SmoothPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : updatedPoints
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Just absCp2x
          , pathStateLastCpY = Just absCp2y
          }
      in
        processSmooth rest newState
    processSmooth _ s = s
  in
    processSmooth args state

processQuadraticBezier :: PathState -> Bool -> [Double] -> PathState
processQuadraticBezier state isRelative args =
  let
    processQuad [] s = s
    processQuad (qx:qy:x:y:rest) s =
      let
        absQx = qx + (if isRelative then pathStateCurrentX s else 0.0)
        absQy = qy + (if isRelative then pathStateCurrentY s else 0.0)
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        -- Convert quadratic to cubic control points
        -- CP1 = P0 + 2/3 * (Q - P0)
        -- CP2 = P1 + 2/3 * (Q - P1)
        cp1x = pathStateCurrentX s + (2/3) * (absQx - pathStateCurrentX s)
        cp1y = pathStateCurrentY s + (2/3) * (absQy - pathStateCurrentY s)
        cp2x = absX + (2/3) * (absQx - absX)
        cp2y = absY + (2/3) * (absQy - absY)
        
        -- Update previous point's handleOut
        updatedPoints = case pathStatePoints s of
          [] -> []
          (p:ps) ->
            let
              updatedP = p
                { controlPointOutHandle = Just (ControlPointHandle cp1x cp1y)
                , controlPointType = SmoothPoint
                }
            in
              updatedP : ps
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Just (ControlPointHandle cp2x cp2y)
          , controlPointOutHandle = Nothing
          , controlPointType = SmoothPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : updatedPoints
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Just absQx
          , pathStateLastCpY = Just absQy
          }
      in
        processQuad rest newState
    processQuad _ s = s
  in
    processQuad args state

processSmoothQuadratic :: PathState -> Bool -> [Double] -> PathState
processSmoothQuadratic state isRelative args =
  let
    processSmoothQuad [] s = s
    processSmoothQuad (x:y:rest) s =
      let
        -- Reflect last quadratic control point
        (qx, qy) = case (pathStateLastCpX s, pathStateLastCpY s) of
          (Just lx, Just ly) -> (2 * pathStateCurrentX s - lx, 2 * pathStateCurrentY s - ly)
          _ -> (pathStateCurrentX s, pathStateCurrentY s)
        
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        -- Convert to cubic
        cp1x = pathStateCurrentX s + (2/3) * (qx - pathStateCurrentX s)
        cp1y = pathStateCurrentY s + (2/3) * (qy - pathStateCurrentY s)
        cp2x = absX + (2/3) * (qx - absX)
        cp2y = absY + (2/3) * (qy - absY)
        
        -- Update previous point's handleOut
        updatedPoints = case pathStatePoints s of
          [] -> []
          (p:ps) ->
            let
              updatedP = p
                { controlPointOutHandle = Just (ControlPointHandle cp1x cp1y)
                , controlPointType = SmoothPoint
                }
            in
              updatedP : ps
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Just (ControlPointHandle cp2x cp2y)
          , controlPointOutHandle = Nothing
          , controlPointType = SmoothPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : updatedPoints
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Just qx
          , pathStateLastCpY = Just qy
          }
      in
        processSmoothQuad rest newState
    processSmoothQuad _ s = s
  in
    processSmoothQuad args state

processArc :: PathState -> Bool -> [Double] -> PathState
processArc state isRelative args =
  let
    -- Arc - approximate as line to endpoint for simplicity
    -- Full arc support would require complex math
    processArcCoords [] s = s
    processArcCoords (_:_:_:_:_:x:y:rest) s =
      let
        absX = x + (if isRelative then pathStateCurrentX s else 0.0)
        absY = y + (if isRelative then pathStateCurrentY s else 0.0)
        
        newPoint = ControlPoint
          { controlPointId = T.pack ("cp_" ++ show (pathStatePathIdx s) ++ "_" ++ show (pathStatePointIdx s))
          , controlPointX = absX
          , controlPointY = absY
          , controlPointInHandle = Nothing
          , controlPointOutHandle = Nothing
          , controlPointType = CornerPoint
          }
        
        newState = s
          { pathStateCurrentX = absX
          , pathStateCurrentY = absY
          , pathStatePoints = newPoint : pathStatePoints s
          , pathStatePointIdx = pathStatePointIdx s + 1
          , pathStateLastCpX = Nothing
          , pathStateLastCpY = Nothing
          }
      in
        processArcCoords rest newState
    processArcCoords _ s = s
  in
    processArcCoords args state

processClosePath :: PathState -> PathState
processClosePath state =
  state
    { pathStateClosed = True
    , pathStateCurrentX = pathStateStartX state
    , pathStateCurrentY = pathStateStartY state
    , pathStateLastCpX = Nothing
    , pathStateLastCpY = Nothing
    }

