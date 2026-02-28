-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // component // qr-code
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Code Component — Pure PureScript QR Code Generation
-- |
-- | ## Design Philosophy
-- |
-- | Complete QR code generation in pure PureScript. No FFI, no JavaScript
-- | libraries — just deterministic data transformation from content to Element.
-- |
-- | ## Quick Start
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.QRCode as QR
-- |
-- | -- Simple URL QR code
-- | myQR = QR.qrCode (QR.urlContent "https://example.com")
-- |
-- | -- WiFi credentials
-- | wifiQR = QR.qrCode (QR.wifiContent "MyNetwork" "password123" QR.WPA)
-- |
-- | -- With custom styling
-- | styledQR = QR.qrCodeWith
-- |   QR.defaultConfig { errorCorrection = QR.ECHigh }
-- |   (QR.urlContent "https://example.com")
-- | ```
-- |
-- | ## Module Structure
-- |
-- | - **QRCode.Types**: Core types (QRVersion, ErrorCorrection, QRMatrix)
-- | - **QRCode.Content**: Content types (URL, WiFi, Email, Calendar, etc.)
-- | - **QRCode.Encoding**: Data encoding (segments, Reed-Solomon)
-- | - **QRCode.Matrix**: Matrix generation and masking
-- | - **QRCode.Render**: SVG rendering
-- |
-- | ## Architecture
-- |
-- | ```
-- | Content → encode → BitStream → interleave → Matrix → render → Element
-- | ```
-- |
-- | Pure data in, Element out. Deterministic. Same input = same pixels.

module Hydrogen.Element.Compound.QRCode
  ( -- * Main API (re-exported from QRCode.QRCode)
    module QRCodeAPI
  
  -- * Content Constructors (re-exported from Content.Types)
  , module ContentTypes
  
  -- * Core Types (re-exported from Types)
  , module Types
  
  -- * Render Config (re-exported from Render.SVG)
  , module RenderSVG
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Re-export the main QRCode API
import Hydrogen.Element.Compound.QRCode.QRCode
  ( qrCode
  , qrCodeWith
  , QRConfig
  , defaultConfig
  ) as QRCodeAPI

-- Re-export content constructors
import Hydrogen.Element.Compound.QRCode.Content.Types
  ( QRContent
      ( ContentURL
      , ContentEmail
      , ContentPhone
      , ContentSMS
      , ContentWiFi
      , ContentVCard
      , ContentCalendar
      , ContentGeo
      , ContentBitcoin
      , ContentSlack
      , ContentWebhook
      , ContentDeepLink
      , ContentText
      )
  , contentToString
  , urlContent
  , urlWithLabel
  , emailContent
  , emailWithSubject
  , emailWithBody
  , emailFull
  , phoneContent
  , smsContent
  , smsWithBody
  , wifiContent
  , wifiHidden
  , WiFiSecurity(WEP, WPA, WPA2, WPA3, NoPassword)
  , geoContent
  , geoWithAltitude
  , geoWithQuery
  , calendarContent
  , vCardContent
  , vCardFull
  , bitcoinContent
  , bitcoinWithAmount
  , bitcoinFull
  , slackChannel
  , slackUser
  , slackCompose
  , webhookGet
  , webhookPost
  , deepLink
  , deepLinkWithFallback
  , textContent
  ) as ContentTypes

-- Re-export core types
import Hydrogen.Element.Compound.QRCode.Types
  ( QRVersion(QRVersion)
  , mkVersion
  , versionToInt
  , minVersion
  , maxVersion
  , versionSize
  , ErrorCorrection(ECLow, ECMedium, ECQuartile, ECHigh)
  , ecToString
  , ecRecoveryPercent
  , EncodingMode(ModeNumeric, ModeAlphanumeric, ModeByte, ModeKanji, ModeECI)
  , modeIndicator
  , detectMode
  , Module(Dark, Light, Reserved)
  , ModuleType(DataModule, FinderModule, TimingModule, AlignmentModule, FormatModule, VersionModule, QuietModule)
  , isDark
  , isLight
  , isReserved
  , QRMatrix
  , mkMatrix
  , matrixSize
  , getModule
  , setModule
  , rowToArray
  , toNestedArray
  , Capacity
  , getCapacity
  ) as Types

-- Re-export render configuration
import Hydrogen.Element.Compound.QRCode.Render.SVG
  ( renderQRCode
  , renderMatrix
  , RenderConfig
  , defaultRenderConfig
  , ModuleStyle(Classic, Rounded, Dots)
  , QRColors
  , defaultColors
  , invertedColors
  , ModulePosition
  , getDarkModulePositions
  , mapDarkModules
  ) as RenderSVG
