-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // reactive // network-state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NetworkState - connection status and quality atoms.
-- |
-- | Models network connectivity lifecycle for offline-first applications.
-- | Includes connection quality metrics for adaptive UI behavior.

module Hydrogen.Schema.Reactive.NetworkState
  ( -- * Connection Status
    ConnectionStatus(..)
  , isOnline
  , isOffline
  , isReconnecting
  -- * Connection Type
  , ConnectionType(..)
  , isWifi
  , isCellular
  , isEthernet
  , isUnknownType
  -- * Effective Connection Type (Network Information API)
  , EffectiveType(..)
  , isSlow2g
  , is2g
  , is3g
  , is4g
  -- * Connection Quality
  , ConnectionQuality
  , connectionQuality
  , defaultQuality
  , isHighQuality
  , isLowQuality
  , shouldReduceData
  -- * Latency Atoms
  , RoundTripTime(..)
  , rttMs
  , unwrapRtt
  , isLowLatency
  , isHighLatency
  -- * Bandwidth Atoms
  , Downlink(..)
  , downlinkMbps
  , unwrapDownlink
  , isFastDownlink
  , isSlowDownlink
  -- * Network State (Compound)
  , NetworkState
  , networkState
  , defaultNetworkState
  , offlineState
  , canFetch
  , shouldDeferLargeRequests
  , adaptiveImageQuality
  -- * Bounds
  , rttBounds
  , downlinkBounds
  ) where

import Prelude

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // connection status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Network connection status
data ConnectionStatus
  = Online        -- ^ Connected to network
  | Offline       -- ^ No network connection
  | Reconnecting  -- ^ Attempting to restore connection

derive instance eqConnectionStatus :: Eq ConnectionStatus
derive instance ordConnectionStatus :: Ord ConnectionStatus

instance showConnectionStatus :: Show ConnectionStatus where
  show Online = "online"
  show Offline = "offline"
  show Reconnecting = "reconnecting"

isOnline :: ConnectionStatus -> Boolean
isOnline Online = true
isOnline _ = false

isOffline :: ConnectionStatus -> Boolean
isOffline Offline = true
isOffline _ = false

isReconnecting :: ConnectionStatus -> Boolean
isReconnecting Reconnecting = true
isReconnecting _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // connection type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Physical connection type (Navigator.connection.type)
data ConnectionType
  = Wifi          -- ^ WiFi connection
  | Cellular      -- ^ Mobile data connection
  | Ethernet      -- ^ Wired connection
  | Bluetooth     -- ^ Bluetooth tethering
  | Wimax         -- ^ WiMAX connection
  | None          -- ^ No connection
  | UnknownType   -- ^ Type cannot be determined

derive instance eqConnectionType :: Eq ConnectionType
derive instance ordConnectionType :: Ord ConnectionType

instance showConnectionType :: Show ConnectionType where
  show Wifi = "wifi"
  show Cellular = "cellular"
  show Ethernet = "ethernet"
  show Bluetooth = "bluetooth"
  show Wimax = "wimax"
  show None = "none"
  show UnknownType = "unknown"

isWifi :: ConnectionType -> Boolean
isWifi Wifi = true
isWifi _ = false

isCellular :: ConnectionType -> Boolean
isCellular Cellular = true
isCellular _ = false

isEthernet :: ConnectionType -> Boolean
isEthernet Ethernet = true
isEthernet _ = false

isUnknownType :: ConnectionType -> Boolean
isUnknownType UnknownType = true
isUnknownType _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // effective connection type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effective connection type (Network Information API)
-- | Based on measured round-trip time and downlink speed
data EffectiveType
  = Slow2g   -- ^ RTT > 2000ms, downlink < 50 Kbps
  | Ect2g    -- ^ RTT > 1400ms, downlink < 70 Kbps
  | Ect3g    -- ^ RTT > 270ms, downlink < 700 Kbps
  | Ect4g    -- ^ RTT <= 270ms, downlink >= 700 Kbps

derive instance eqEffectiveType :: Eq EffectiveType
derive instance ordEffectiveType :: Ord EffectiveType

instance showEffectiveType :: Show EffectiveType where
  show Slow2g = "slow-2g"
  show Ect2g = "2g"
  show Ect3g = "3g"
  show Ect4g = "4g"

isSlow2g :: EffectiveType -> Boolean
isSlow2g Slow2g = true
isSlow2g _ = false

is2g :: EffectiveType -> Boolean
is2g Ect2g = true
is2g _ = false

is3g :: EffectiveType -> Boolean
is3g Ect3g = true
is3g _ = false

is4g :: EffectiveType -> Boolean
is4g Ect4g = true
is4g _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // latency atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Round-trip time in milliseconds (bounded, non-negative)
newtype RoundTripTime = RoundTripTime Number

derive instance eqRoundTripTime :: Eq RoundTripTime
derive instance ordRoundTripTime :: Ord RoundTripTime

instance showRoundTripTime :: Show RoundTripTime where
  show (RoundTripTime ms) = show ms <> "ms"

-- | Create RTT value (clamps to [0, 30000] ms)
-- |
-- | Maximum is 30 seconds — beyond this, connection is effectively dead.
rttMs :: Number -> RoundTripTime
rttMs ms = RoundTripTime (Bounded.clampNumber 0.0 30000.0 ms)

-- | Extract RTT value
unwrapRtt :: RoundTripTime -> Number
unwrapRtt (RoundTripTime ms) = ms

-- | Is latency low enough for real-time interaction? (< 100ms)
isLowLatency :: RoundTripTime -> Boolean
isLowLatency (RoundTripTime ms) = ms < 100.0

-- | Is latency high enough to cause perceived delay? (> 300ms)
isHighLatency :: RoundTripTime -> Boolean
isHighLatency (RoundTripTime ms) = ms > 300.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bandwidth atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Downlink bandwidth in megabits per second
newtype Downlink = Downlink Number

derive instance eqDownlink :: Eq Downlink
derive instance ordDownlink :: Ord Downlink

instance showDownlink :: Show Downlink where
  show (Downlink mbps) = show mbps <> " Mbps"

-- | Create downlink value (clamps to [0, 10000] Mbps)
-- |
-- | Maximum is 10 Gbps — beyond current consumer technology.
downlinkMbps :: Number -> Downlink
downlinkMbps mbps = Downlink (Bounded.clampNumber 0.0 10000.0 mbps)

-- | Extract downlink value
unwrapDownlink :: Downlink -> Number
unwrapDownlink (Downlink mbps) = mbps

-- | Is bandwidth fast enough for high-quality media? (> 5 Mbps)
isFastDownlink :: Downlink -> Boolean
isFastDownlink (Downlink mbps) = mbps > 5.0

-- | Is bandwidth too slow for comfortable browsing? (< 1 Mbps)
isSlowDownlink :: Downlink -> Boolean
isSlowDownlink (Downlink mbps) = mbps < 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // connection quality molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Connection quality metrics
type ConnectionQuality =
  { effectiveType :: EffectiveType
  , rtt :: RoundTripTime
  , downlink :: Downlink
  , saveData :: Boolean        -- ^ User has requested reduced data usage
  }

-- | Create connection quality
connectionQuality :: EffectiveType -> RoundTripTime -> Downlink -> Boolean -> ConnectionQuality
connectionQuality effectiveType rtt downlink saveData =
  { effectiveType, rtt, downlink, saveData }

-- | Default quality (assume good connection)
defaultQuality :: ConnectionQuality
defaultQuality =
  { effectiveType: Ect4g
  , rtt: rttMs 50.0
  , downlink: downlinkMbps 10.0
  , saveData: false
  }

-- | Is connection quality good? (4g and fast)
isHighQuality :: ConnectionQuality -> Boolean
isHighQuality q = 
  is4g q.effectiveType && 
  isLowLatency q.rtt && 
  isFastDownlink q.downlink

-- | Is connection quality poor? (slow-2g/2g or high latency)
isLowQuality :: ConnectionQuality -> Boolean
isLowQuality q =
  isSlow2g q.effectiveType ||
  is2g q.effectiveType ||
  isHighLatency q.rtt ||
  isSlowDownlink q.downlink

-- | Should reduce data usage? (save-data or low quality)
shouldReduceData :: ConnectionQuality -> Boolean
shouldReduceData q = q.saveData || isLowQuality q

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // network state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete network state for application
type NetworkState =
  { status :: ConnectionStatus
  , connectionType :: ConnectionType
  , quality :: ConnectionQuality
  , lastOnlineAt :: Maybe Number      -- ^ Unix timestamp of last online
  , reconnectAttempts :: Int          -- ^ Number of reconnection attempts
  , wasOffline :: Boolean             -- ^ Has been offline this session
  }

-- | Create network state
networkState :: ConnectionStatus -> ConnectionType -> ConnectionQuality -> NetworkState
networkState status connectionType quality =
  { status
  , connectionType
  , quality
  , lastOnlineAt: Nothing
  , reconnectAttempts: 0
  , wasOffline: false
  }

-- | Default network state (online, wifi, good quality)
defaultNetworkState :: NetworkState
defaultNetworkState = networkState Online Wifi defaultQuality

-- | Offline network state
offlineState :: NetworkState
offlineState =
  { status: Offline
  , connectionType: None
  , quality: defaultQuality  -- Quality unknown when offline
  , lastOnlineAt: Nothing
  , reconnectAttempts: 0
  , wasOffline: true
  }

-- | Can application make network requests?
canFetch :: NetworkState -> Boolean
canFetch ns = isOnline ns.status

-- | Should defer large requests? (offline, reconnecting, or slow)
shouldDeferLargeRequests :: NetworkState -> Boolean
shouldDeferLargeRequests ns =
  not (isOnline ns.status) || 
  shouldReduceData ns.quality

-- | Recommended image quality based on network (0.0 - 1.0)
adaptiveImageQuality :: NetworkState -> Number
adaptiveImageQuality ns
  | not (isOnline ns.status) = 0.0  -- Don't fetch when offline
  | isSlow2g ns.quality.effectiveType = 0.25
  | is2g ns.quality.effectiveType = 0.5
  | is3g ns.quality.effectiveType = 0.75
  | shouldReduceData ns.quality = 0.5
  | otherwise = 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for RoundTripTime [0, 30000] ms
-- |
-- | - 0ms: Theoretical perfect latency (impossible, but valid floor)
-- | - 30000ms: 30 seconds — connection is effectively dead beyond this
rttBounds :: Bounded.NumberBounds
rttBounds = Bounded.numberBounds 0.0 30000.0 "RoundTripTime"
  "Network round-trip latency in milliseconds (0-30s)"

-- | Bounds for Downlink [0, 10000] Mbps
-- |
-- | - 0 Mbps: No bandwidth (offline)
-- | - 10000 Mbps: 10 Gbps — beyond current consumer technology
downlinkBounds :: Bounded.NumberBounds
downlinkBounds = Bounded.numberBounds 0.0 10000.0 "Downlink"
  "Download bandwidth in megabits per second (0-10 Gbps)"
