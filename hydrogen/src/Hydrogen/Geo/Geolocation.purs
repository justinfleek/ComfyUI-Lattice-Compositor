-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // geolocation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geolocation services
-- |
-- | Access to device geolocation with position tracking, distance calculations,
-- | and geofencing support.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Geo.Geolocation as Geo
-- |
-- | -- Get current position (one-time)
-- | result <- Geo.getCurrentPosition Geo.defaultOptions
-- | case result of
-- |   Right pos -> Console.log $ "Lat: " <> show pos.latitude
-- |   Left err -> Console.log $ "Error: " <> Geo.errorMessage err
-- |
-- | -- Watch position (continuous updates)
-- | unwatch <- Geo.watchPosition
-- |   [ Geo.highAccuracy true
-- |   , Geo.timeout 10000
-- |   ]
-- |   \result -> case result of
-- |     Right pos -> updateMarker pos
-- |     Left err -> showError err
-- |
-- | -- Later, stop watching
-- | unwatch
-- |
-- | -- Calculate distance between two points
-- | let distance = Geo.haversineDistance pos1 pos2
-- | Console.log $ "Distance: " <> show distance <> " meters"
-- |
-- | -- Calculate bearing
-- | let bearing = Geo.calculateBearing pos1 pos2
-- | Console.log $ "Bearing: " <> show bearing <> " degrees"
-- |
-- | -- Geofencing
-- | unsubscribe <- Geo.watchGeofence
-- |   { center: { latitude: 51.505, longitude: -0.09 }
-- |   , radius: 100.0  -- meters
-- |   }
-- |   \event -> case event of
-- |     Geo.Enter -> Console.log "Entered zone"
-- |     Geo.Exit -> Console.log "Exited zone"
-- | ```
module Hydrogen.Geo.Geolocation
  ( -- * Position Types
    Position
  , Coordinates
  , LatLon
    -- * Options
  , PositionOptions
  , PositionOption
  , defaultOptions
  , highAccuracy
  , timeout
  , maximumAge
    -- * Error Types
  , PositionError(PermissionDenied, PositionUnavailable, Timeout, UnknownError)
  , errorMessage
  , errorCode
    -- * Getting Position
  , getCurrentPosition
  , watchPosition
  , clearWatch
  , WatchId
    -- * Distance Calculations
  , haversineDistance
  , calculateBearing
  , destinationPoint
  , midpoint
    -- * Speed and Heading
  , getSpeed
  , getHeading
  , SpeedInfo
  , HeadingInfo
    -- * Geofencing
  , Geofence
  , GeofenceEvent(Enter, Exit, Dwell)
  , watchGeofence
  , createGeofence
  , isInsideGeofence
    -- * Utilities
  , isSupported
  , toLatLng
  , fromLatLng
  , formatCoordinates
  , formatDistance
  ) where

import Prelude

import Data.Array (foldl)
import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Int (toNumber)
import Data.Number (abs, acos, asin, atan2, cos, pi, pow, sin, sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geographic coordinates with latitude and longitude
type LatLon =
  { latitude :: Number
  , longitude :: Number
  }

-- | Full coordinates including altitude and accuracy
type Coordinates =
  { latitude :: Number
  , longitude :: Number
  , altitude :: Maybe Number
  , accuracy :: Number
  , altitudeAccuracy :: Maybe Number
  , heading :: Maybe Number
  , speed :: Maybe Number
  }

-- | Full position including timestamp
type Position =
  { coords :: Coordinates
  , timestamp :: Number
  }

-- | Speed information
type SpeedInfo =
  { speed :: Number          -- meters per second
  , speedKmh :: Number       -- kilometers per hour
  , speedMph :: Number       -- miles per hour
  }

-- | Heading/compass information
type HeadingInfo =
  { heading :: Number        -- degrees from north (0-360)
  , magneticHeading :: Maybe Number
  , accuracy :: Maybe Number
  }

-- | Watch subscription ID
newtype WatchId = WatchId Int

derive instance eqWatchId :: Eq WatchId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // errors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geolocation error types
data PositionError
  = PermissionDenied
  | PositionUnavailable
  | Timeout
  | UnknownError String

derive instance eqPositionError :: Eq PositionError

instance showPositionError :: Show PositionError where
  show PermissionDenied = "PermissionDenied"
  show PositionUnavailable = "PositionUnavailable"
  show Timeout = "Timeout"
  show (UnknownError msg) = "UnknownError: " <> msg

-- | Get human-readable error message
errorMessage :: PositionError -> String
errorMessage PermissionDenied = "Location permission was denied. Please allow location access in your browser settings."
errorMessage PositionUnavailable = "Your location could not be determined. Please check your device's location services."
errorMessage Timeout = "Location request timed out. Please try again."
errorMessage (UnknownError msg) = "Location error: " <> msg

-- | Get error code number
errorCode :: PositionError -> Int
errorCode PermissionDenied = 1
errorCode PositionUnavailable = 2
errorCode Timeout = 3
errorCode (UnknownError _) = 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position request options
type PositionOptions =
  { enableHighAccuracy :: Boolean
  , timeout :: Int
  , maximumAge :: Int
  }

type PositionOption = PositionOptions -> PositionOptions

-- | Default position options
defaultOptions :: PositionOptions
defaultOptions =
  { enableHighAccuracy: false
  , timeout: 10000
  , maximumAge: 0
  }

-- | Enable high accuracy mode (uses GPS, more battery)
highAccuracy :: Boolean -> PositionOption
highAccuracy enabled opts = opts { enableHighAccuracy = enabled }

-- | Set timeout in milliseconds
timeout :: Int -> PositionOption
timeout ms opts = opts { timeout = ms }

-- | Set maximum age of cached position in milliseconds
maximumAge :: Int -> PositionOption
maximumAge ms opts = opts { maximumAge = ms }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // getting position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if geolocation is supported
foreign import isSupportedImpl :: Effect Boolean

isSupported :: Effect Boolean
isSupported = isSupportedImpl

-- | Get current position (one-time)
getCurrentPosition :: Array PositionOption -> Aff (Either PositionError Position)
getCurrentPosition optMods = fromEffectFnAff $ getCurrentPositionImpl opts
  where
  opts = foldl (\o f -> f o) defaultOptions optMods

foreign import getCurrentPositionImpl :: PositionOptions -> EffectFnAff (Either PositionError Position)

-- | Watch position with continuous updates
watchPosition 
  :: Array PositionOption 
  -> (Either PositionError Position -> Effect Unit) 
  -> Effect (Effect Unit)
watchPosition optMods callback = do
  watchId <- watchPositionImpl opts callback
  pure $ clearWatchImpl watchId
  where
  opts = foldl (\o f -> f o) defaultOptions optMods

foreign import watchPositionImpl 
  :: PositionOptions 
  -> (Either PositionError Position -> Effect Unit) 
  -> Effect WatchId

-- | Clear a position watch
clearWatch :: WatchId -> Effect Unit
clearWatch = clearWatchImpl

foreign import clearWatchImpl :: WatchId -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // distance calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Earth radius in meters
earthRadius :: Number
earthRadius = 6371000.0

-- | Convert degrees to radians
toRadians :: Number -> Number
toRadians deg = deg * pi / 180.0

-- | Convert radians to degrees
toDegrees :: Number -> Number
toDegrees rad = rad * 180.0 / pi

-- | Calculate distance between two points using Haversine formula
-- | Returns distance in meters
haversineDistance :: LatLon -> LatLon -> Number
haversineDistance p1 p2 =
  let
    lat1 = toRadians p1.latitude
    lat2 = toRadians p2.latitude
    dLat = toRadians (p2.latitude - p1.latitude)
    dLon = toRadians (p2.longitude - p1.longitude)
    
    a = sin(dLat / 2.0) * sin(dLat / 2.0) +
        cos(lat1) * cos(lat2) * sin(dLon / 2.0) * sin(dLon / 2.0)
    c = 2.0 * atan2 (sqrt a) (sqrt (1.0 - a))
  in
    earthRadius * c

-- | Calculate bearing from point 1 to point 2
-- | Returns bearing in degrees (0-360, 0 = north)
calculateBearing :: LatLon -> LatLon -> Number
calculateBearing p1 p2 =
  let
    lat1 = toRadians p1.latitude
    lat2 = toRadians p2.latitude
    dLon = toRadians (p2.longitude - p1.longitude)
    
    y = sin(dLon) * cos(lat2)
    x = cos(lat1) * sin(lat2) - sin(lat1) * cos(lat2) * cos(dLon)
    bearing = toDegrees (atan2 y x)
  in
    mod' (bearing + 360.0) 360.0

-- | Calculate destination point given start, bearing, and distance
-- | Distance in meters, bearing in degrees
destinationPoint :: LatLon -> Number -> Number -> LatLon
destinationPoint start bearing distance =
  let
    lat1 = toRadians start.latitude
    lon1 = toRadians start.longitude
    brng = toRadians bearing
    d = distance / earthRadius
    
    lat2 = asin (sin(lat1) * cos(d) + cos(lat1) * sin(d) * cos(brng))
    lon2 = lon1 + atan2 (sin(brng) * sin(d) * cos(lat1)) 
                        (cos(d) - sin(lat1) * sin(lat2))
  in
    { latitude: toDegrees lat2
    , longitude: toDegrees lon2
    }

-- | Calculate midpoint between two points
midpoint :: LatLon -> LatLon -> LatLon
midpoint p1 p2 =
  let
    lat1 = toRadians p1.latitude
    lon1 = toRadians p1.longitude
    lat2 = toRadians p2.latitude
    dLon = toRadians (p2.longitude - p1.longitude)
    
    bx = cos(lat2) * cos(dLon)
    by = cos(lat2) * sin(dLon)
    
    lat3 = atan2 (sin(lat1) + sin(lat2)) 
                 (sqrt ((cos(lat1) + bx) * (cos(lat1) + bx) + by * by))
    lon3 = lon1 + atan2 by (cos(lat1) + bx)
  in
    { latitude: toDegrees lat3
    , longitude: toDegrees lon3
    }

-- | Modulo for floating point numbers
mod' :: Number -> Number -> Number
mod' x y = x - y * (floor' (x / y))
  where
  floor' n = if n >= 0.0 then floorImpl n else ceilImpl n

foreign import floorImpl :: Number -> Number
foreign import ceilImpl :: Number -> Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // speed and heading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get speed info from position
getSpeed :: Position -> Maybe SpeedInfo
getSpeed pos = case pos.coords.speed of
  Nothing -> Nothing
  Just s -> Just
    { speed: s
    , speedKmh: s * 3.6
    , speedMph: s * 2.237
    }

-- | Get heading info from position
getHeading :: Position -> Maybe HeadingInfo
getHeading pos = case pos.coords.heading of
  Nothing -> Nothing
  Just h -> Just
    { heading: h
    , magneticHeading: Nothing  -- Not available in standard API
    , accuracy: Nothing
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // geofencing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geofence definition (circular zone)
type Geofence =
  { center :: LatLon
  , radius :: Number  -- meters
  , id :: String
  }

-- | Geofence events
data GeofenceEvent
  = Enter
  | Exit
  | Dwell

derive instance eqGeofenceEvent :: Eq GeofenceEvent

instance showGeofenceEvent :: Show GeofenceEvent where
  show Enter = "Enter"
  show Exit = "Exit"
  show Dwell = "Dwell"

-- | Create a geofence
createGeofence :: String -> LatLon -> Number -> Geofence
createGeofence id c r =
  { center: c
  , radius: r
  , id: id
  }

-- | Check if a position is inside a geofence
isInsideGeofence :: LatLon -> Geofence -> Boolean
isInsideGeofence pos fence =
  haversineDistance pos fence.center <= fence.radius

-- | Watch a geofence for enter/exit events
watchGeofence 
  :: Geofence 
  -> (GeofenceEvent -> Effect Unit) 
  -> Effect (Effect Unit)
watchGeofence fence callback = watchGeofenceImpl fence callback

foreign import watchGeofenceImpl 
  :: Geofence 
  -> (GeofenceEvent -> Effect Unit) 
  -> Effect (Effect Unit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Position to simple LatLon
toLatLng :: Position -> LatLon
toLatLng pos =
  { latitude: pos.coords.latitude
  , longitude: pos.coords.longitude
  }

-- | Convert LatLon to Coordinates (with defaults)
fromLatLng :: LatLon -> Coordinates
fromLatLng ll =
  { latitude: ll.latitude
  , longitude: ll.longitude
  , altitude: Nothing
  , accuracy: 0.0
  , altitudeAccuracy: Nothing
  , heading: Nothing
  , speed: Nothing
  }

-- | Format coordinates for display
formatCoordinates :: LatLon -> String
formatCoordinates ll =
  formatDegrees ll.latitude (if ll.latitude >= 0.0 then "N" else "S")
  <> ", "
  <> formatDegrees ll.longitude (if ll.longitude >= 0.0 then "E" else "W")
  where
  formatDegrees deg dir =
    show (roundTo (abs deg) 6) <> "° " <> dir

-- | Format distance for display
formatDistance :: Number -> String
formatDistance meters
  | meters < 1000.0 = show (round' meters) <> " m"
  | otherwise = show (roundTo (meters / 1000.0) 2) <> " km"

-- | Round to decimal places
roundTo :: Number -> Int -> Number
roundTo n places =
  let multiplier = pow 10.0 (toNumber places)
  in round' (n * multiplier) / multiplier

round' :: Number -> Number
round' = roundImpl

foreign import roundImpl :: Number -> Number
