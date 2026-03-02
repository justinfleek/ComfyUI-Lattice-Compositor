-- |
-- Module      : Lattice.Types.Presets.BuiltInPresets
-- Description : Built-in preset definitions
-- 
-- Migrated from ui/src/types/presets.ts BUILT_IN_PARTICLE_PRESETS and BUILT_IN_PATH_EFFECT_PRESETS
-- Built-in presets for particles and path effects
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.Presets.BuiltInPresets
  ( builtInParticlePresets,
    builtInPathEffectPresets,
  )
where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Presets.Core
  ( ParticlePreset (..),
    ParticlePresetConfig (..),
    PathEffectPreset (..),
    PresetCategory (..),
    PresetMetadata (..),
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // built
-- ════════════════════════════════════════════════════════════════════════════

-- | Built-in particle presets
--                                                                      // note
builtInParticlePresets :: [ParticlePreset]
builtInParticlePresets =
  [ ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-fire",
              presetMetadataName = "Fire",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Flickering flame effect",
              presetMetadataTags = Just ["fire", "flame", "hot"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0, -- Placeholder - set at runtime
              presetMetadataUpdatedAt = 0.0, -- Placeholder - set at runtime
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 500.0,
              particlePresetConfigEmissionRate = Just 50.0,
              particlePresetConfigLifespan = Just 1.5,
              particlePresetConfigStartSize = Just 20.0,
              particlePresetConfigEndSize = Just 5.0,
              particlePresetConfigStartColor = Just "#ff6600",
              particlePresetConfigEndColor = Just "#ffff00",
              particlePresetConfigGravity = Just (-50.0),
              particlePresetConfigTurbulenceStrength = Just 30.0,
              particlePresetConfigVelocitySpread = Just 30.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-snow",
              presetMetadataName = "Snow",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Gentle falling snowflakes",
              presetMetadataTags = Just ["snow", "winter", "cold"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 300.0,
              particlePresetConfigEmissionRate = Just 20.0,
              particlePresetConfigLifespan = Just 5.0,
              particlePresetConfigStartSize = Just 8.0,
              particlePresetConfigEndSize = Just 6.0,
              particlePresetConfigStartColor = Just "#ffffff",
              particlePresetConfigEndColor = Just "#ccccff",
              particlePresetConfigGravity = Just 20.0,
              particlePresetConfigTurbulenceStrength = Just 10.0,
              particlePresetConfigVelocitySpread = Just 20.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-sparks",
              presetMetadataName = "Sparks",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Electric spark burst",
              presetMetadataTags = Just ["sparks", "electric", "energy"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 200.0,
              particlePresetConfigEmissionRate = Just 100.0,
              particlePresetConfigLifespan = Just 0.5,
              particlePresetConfigStartSize = Just 4.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#ffff00",
              particlePresetConfigEndColor = Just "#ff8800",
              particlePresetConfigGravity = Just 100.0,
              particlePresetConfigTurbulenceStrength = Nothing,
              particlePresetConfigVelocitySpread = Just 180.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-smoke",
              presetMetadataName = "Smoke",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Rising smoke plume",
              presetMetadataTags = Just ["smoke", "fog", "mist"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 100.0,
              particlePresetConfigEmissionRate = Just 10.0,
              particlePresetConfigLifespan = Just 4.0,
              particlePresetConfigStartSize = Just 30.0,
              particlePresetConfigEndSize = Just 80.0,
              particlePresetConfigStartColor = Just "#444444",
              particlePresetConfigEndColor = Just "#888888",
              particlePresetConfigGravity = Just (-30.0),
              particlePresetConfigTurbulenceStrength = Just 20.0,
              particlePresetConfigVelocitySpread = Nothing
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-confetti",
              presetMetadataName = "Confetti",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Colorful celebration confetti",
              presetMetadataTags = Just ["confetti", "celebration", "party"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 500.0,
              particlePresetConfigEmissionRate = Just 100.0,
              particlePresetConfigLifespan = Just 3.0,
              particlePresetConfigStartSize = Just 10.0,
              particlePresetConfigEndSize = Just 8.0,
              particlePresetConfigStartColor = Nothing,
              particlePresetConfigEndColor = Nothing,
              particlePresetConfigGravity = Just 50.0,
              particlePresetConfigTurbulenceStrength = Just 15.0,
              particlePresetConfigVelocitySpread = Just 60.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-rain",
              presetMetadataName = "Rain",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Falling rain drops",
              presetMetadataTags = Just ["rain", "weather", "water"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 1000.0,
              particlePresetConfigEmissionRate = Just 200.0,
              particlePresetConfigLifespan = Just 1.5,
              particlePresetConfigStartSize = Just 3.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#88bbff",
              particlePresetConfigEndColor = Just "#6699cc",
              particlePresetConfigGravity = Just 400.0,
              particlePresetConfigTurbulenceStrength = Nothing,
              particlePresetConfigVelocitySpread = Just 5.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-dust",
              presetMetadataName = "Dust",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Floating dust motes",
              presetMetadataTags = Just ["dust", "ambient", "atmosphere"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 200.0,
              particlePresetConfigEmissionRate = Just 5.0,
              particlePresetConfigLifespan = Just 8.0,
              particlePresetConfigStartSize = Just 2.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#ccccbb",
              particlePresetConfigEndColor = Just "#888877",
              particlePresetConfigGravity = Just (-2.0),
              particlePresetConfigTurbulenceStrength = Just 5.0,
              particlePresetConfigVelocitySpread = Just 360.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-magic",
              presetMetadataName = "Magic Sparkle",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Magical glowing particles",
              presetMetadataTags = Just ["magic", "sparkle", "glow", "fantasy"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 300.0,
              particlePresetConfigEmissionRate = Just 30.0,
              particlePresetConfigLifespan = Just 2.0,
              particlePresetConfigStartSize = Just 8.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#ff88ff",
              particlePresetConfigEndColor = Just "#8844ff",
              particlePresetConfigGravity = Just (-20.0),
              particlePresetConfigTurbulenceStrength = Just 25.0,
              particlePresetConfigVelocitySpread = Just 180.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-bubbles",
              presetMetadataName = "Bubbles",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Rising soap bubbles",
              presetMetadataTags = Just ["bubbles", "water", "soap"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 100.0,
              particlePresetConfigEmissionRate = Just 8.0,
              particlePresetConfigLifespan = Just 4.0,
              particlePresetConfigStartSize = Just 15.0,
              particlePresetConfigEndSize = Just 25.0,
              particlePresetConfigStartColor = Just "#aaddff",
              particlePresetConfigEndColor = Just "#ffffff",
              particlePresetConfigGravity = Just (-30.0),
              particlePresetConfigTurbulenceStrength = Just 15.0,
              particlePresetConfigVelocitySpread = Just 30.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-leaves",
              presetMetadataName = "Falling Leaves",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Autumn leaves floating down",
              presetMetadataTags = Just ["leaves", "autumn", "nature", "fall"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 150.0,
              particlePresetConfigEmissionRate = Just 10.0,
              particlePresetConfigLifespan = Just 5.0,
              particlePresetConfigStartSize = Just 12.0,
              particlePresetConfigEndSize = Just 10.0,
              particlePresetConfigStartColor = Just "#dd8833",
              particlePresetConfigEndColor = Just "#884422",
              particlePresetConfigGravity = Just 25.0,
              particlePresetConfigTurbulenceStrength = Just 40.0,
              particlePresetConfigVelocitySpread = Just 45.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-stars",
              presetMetadataName = "Twinkling Stars",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Starfield with twinkling effect",
              presetMetadataTags = Just ["stars", "night", "space", "twinkle"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 300.0,
              particlePresetConfigEmissionRate = Just 15.0,
              particlePresetConfigLifespan = Just 3.0,
              particlePresetConfigStartSize = Just 4.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#ffffff",
              particlePresetConfigEndColor = Just "#ffffcc",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 2.0,
              particlePresetConfigVelocitySpread = Just 360.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-fireworks",
              presetMetadataName = "Fireworks",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Explosive firework burst",
              presetMetadataTags = Just ["fireworks", "explosion", "celebration"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 500.0,
              particlePresetConfigEmissionRate = Just 200.0,
              particlePresetConfigLifespan = Just 1.5,
              particlePresetConfigStartSize = Just 6.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#ffff00",
              particlePresetConfigEndColor = Just "#ff4400",
              particlePresetConfigGravity = Just 100.0,
              particlePresetConfigTurbulenceStrength = Nothing,
              particlePresetConfigVelocitySpread = Just 180.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-aurora",
              presetMetadataName = "Aurora",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Northern lights effect",
              presetMetadataTags = Just ["aurora", "northern lights", "glow"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 200.0,
              particlePresetConfigEmissionRate = Just 20.0,
              particlePresetConfigLifespan = Just 4.0,
              particlePresetConfigStartSize = Just 30.0,
              particlePresetConfigEndSize = Just 50.0,
              particlePresetConfigStartColor = Just "#00ff88",
              particlePresetConfigEndColor = Just "#8844ff",
              particlePresetConfigGravity = Just (-5.0),
              particlePresetConfigTurbulenceStrength = Just 30.0,
              particlePresetConfigVelocitySpread = Just 20.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-embers",
              presetMetadataName = "Embers",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Glowing fire embers",
              presetMetadataTags = Just ["embers", "fire", "glow", "heat"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 150.0,
              particlePresetConfigEmissionRate = Just 25.0,
              particlePresetConfigLifespan = Just 3.0,
              particlePresetConfigStartSize = Just 4.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#ff6622",
              particlePresetConfigEndColor = Just "#441100",
              particlePresetConfigGravity = Just (-40.0),
              particlePresetConfigTurbulenceStrength = Just 20.0,
              particlePresetConfigVelocitySpread = Just 30.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-fog",
              presetMetadataName = "Dense Fog",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Thick rolling fog",
              presetMetadataTags = Just ["fog", "mist", "atmosphere", "weather"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 50.0,
              particlePresetConfigEmissionRate = Just 3.0,
              particlePresetConfigLifespan = Just 10.0,
              particlePresetConfigStartSize = Just 100.0,
              particlePresetConfigEndSize = Just 200.0,
              particlePresetConfigStartColor = Just "#888888",
              particlePresetConfigEndColor = Just "#666666",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 10.0,
              particlePresetConfigVelocitySpread = Just 20.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-explosion",
              presetMetadataName = "Explosion",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Violent debris explosion",
              presetMetadataTags = Just ["explosion", "debris", "blast"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 300.0,
              particlePresetConfigEmissionRate = Just 500.0,
              particlePresetConfigLifespan = Just 0.8,
              particlePresetConfigStartSize = Just 10.0,
              particlePresetConfigEndSize = Just 3.0,
              particlePresetConfigStartColor = Just "#ffaa00",
              particlePresetConfigEndColor = Just "#331100",
              particlePresetConfigGravity = Just 150.0,
              particlePresetConfigTurbulenceStrength = Nothing,
              particlePresetConfigVelocitySpread = Just 180.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-portal",
              presetMetadataName = "Portal Swirl",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Magical portal vortex",
              presetMetadataTags = Just ["portal", "vortex", "magic", "swirl"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 400.0,
              particlePresetConfigEmissionRate = Just 60.0,
              particlePresetConfigLifespan = Just 2.0,
              particlePresetConfigStartSize = Just 6.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#00ddff",
              particlePresetConfigEndColor = Just "#4400ff",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 15.0,
              particlePresetConfigVelocitySpread = Just 30.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-electricity",
              presetMetadataName = "Electricity",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Electric arcs and sparks",
              presetMetadataTags = Just ["electricity", "lightning", "energy"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 200.0,
              particlePresetConfigEmissionRate = Just 150.0,
              particlePresetConfigLifespan = Just 0.3,
              particlePresetConfigStartSize = Just 3.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#aaeeff",
              particlePresetConfigEndColor = Just "#ffffff",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 50.0,
              particlePresetConfigVelocitySpread = Just 180.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-hearts",
              presetMetadataName = "Hearts",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Floating heart particles",
              presetMetadataTags = Just ["hearts", "love", "romance", "valentine"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 100.0,
              particlePresetConfigEmissionRate = Just 15.0,
              particlePresetConfigLifespan = Just 3.0,
              particlePresetConfigStartSize = Just 15.0,
              particlePresetConfigEndSize = Just 8.0,
              particlePresetConfigStartColor = Just "#ff4466",
              particlePresetConfigEndColor = Just "#ff88aa",
              particlePresetConfigGravity = Just (-25.0),
              particlePresetConfigTurbulenceStrength = Just 10.0,
              particlePresetConfigVelocitySpread = Just 60.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-waterfall",
              presetMetadataName = "Waterfall",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Cascading water effect",
              presetMetadataTags = Just ["water", "waterfall", "cascade", "splash"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 600.0,
              particlePresetConfigEmissionRate = Just 150.0,
              particlePresetConfigLifespan = Just 1.2,
              particlePresetConfigStartSize = Just 5.0,
              particlePresetConfigEndSize = Just 8.0,
              particlePresetConfigStartColor = Just "#aaddff",
              particlePresetConfigEndColor = Just "#ffffff",
              particlePresetConfigGravity = Just 300.0,
              particlePresetConfigTurbulenceStrength = Just 10.0,
              particlePresetConfigVelocitySpread = Just 15.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-fireflies",
              presetMetadataName = "Fireflies",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Gently glowing fireflies",
              presetMetadataTags = Just ["fireflies", "glow", "nature", "night"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 50.0,
              particlePresetConfigEmissionRate = Just 3.0,
              particlePresetConfigLifespan = Just 6.0,
              particlePresetConfigStartSize = Just 5.0,
              particlePresetConfigEndSize = Just 3.0,
              particlePresetConfigStartColor = Just "#ccff66",
              particlePresetConfigEndColor = Just "#669933",
              particlePresetConfigGravity = Just (-5.0),
              particlePresetConfigTurbulenceStrength = Just 20.0,
              particlePresetConfigVelocitySpread = Just 360.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-sandstorm",
              presetMetadataName = "Sandstorm",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Blowing desert sand",
              presetMetadataTags = Just ["sand", "desert", "storm", "wind"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 800.0,
              particlePresetConfigEmissionRate = Just 200.0,
              particlePresetConfigLifespan = Just 2.0,
              particlePresetConfigStartSize = Just 3.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#cc9966",
              particlePresetConfigEndColor = Just "#886644",
              particlePresetConfigGravity = Just 20.0,
              particlePresetConfigTurbulenceStrength = Just 60.0,
              particlePresetConfigVelocitySpread = Just 30.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-glitter",
              presetMetadataName = "Glitter",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription = Just "Shimmering glitter particles",
              presetMetadataTags = Just ["glitter", "sparkle", "shine"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 400.0,
              particlePresetConfigEmissionRate = Just 80.0,
              particlePresetConfigLifespan = Just 1.5,
              particlePresetConfigStartSize = Just 3.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#ffffff",
              particlePresetConfigEndColor = Just "#ffdd88",
              particlePresetConfigGravity = Just 30.0,
              particlePresetConfigTurbulenceStrength = Just 8.0,
              particlePresetConfigVelocitySpread = Just 120.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-path-light",
              presetMetadataName = "Path Light",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription =
                Just "Glowing lights that follow spline edges - perfect for logo edge tracing",
              presetMetadataTags =
                Just
                  [ "path",
                    "light",
                    "glow",
                    "edge",
                    "trace",
                    "logo",
                    "outline",
                    "neon"
                  ],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 200.0,
              particlePresetConfigEmissionRate = Just 40.0,
              particlePresetConfigLifespan = Just 2.5,
              particlePresetConfigStartSize = Just 6.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#ffffff",
              particlePresetConfigEndColor = Just "#00ffff",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 3.0,
              particlePresetConfigVelocitySpread = Just 15.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-path-light-warm",
              presetMetadataName = "Path Light (Warm)",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription =
                Just "Warm glowing lights for edge tracing - gold/amber variant",
              presetMetadataTags = Just ["path", "light", "glow", "edge", "warm", "gold", "amber"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 200.0,
              particlePresetConfigEmissionRate = Just 40.0,
              particlePresetConfigLifespan = Just 2.5,
              particlePresetConfigStartSize = Just 6.0,
              particlePresetConfigEndSize = Just 2.0,
              particlePresetConfigStartColor = Just "#ffffff",
              particlePresetConfigEndColor = Just "#ffaa00",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 3.0,
              particlePresetConfigVelocitySpread = Just 15.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-path-light-neon",
              presetMetadataName = "Path Light (Neon)",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription =
                Just "Intense neon lights for edge tracing - magenta/pink variant",
              presetMetadataTags = Just ["path", "light", "glow", "edge", "neon", "pink", "magenta"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 300.0,
              particlePresetConfigEmissionRate = Just 60.0,
              particlePresetConfigLifespan = Just 1.8,
              particlePresetConfigStartSize = Just 8.0,
              particlePresetConfigEndSize = Just 3.0,
              particlePresetConfigStartColor = Just "#ff88ff",
              particlePresetConfigEndColor = Just "#ff00ff",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 5.0,
              particlePresetConfigVelocitySpread = Just 20.0
            }
      },
    ParticlePreset
      { particlePresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-particle-path-comet",
              presetMetadataName = "Path Comet",
              presetMetadataCategory = PresetCategoryParticle,
              presetMetadataDescription =
                Just "Comet-like particles with long trails - great for motion paths",
              presetMetadataTags = Just ["path", "comet", "trail", "motion", "streak"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        particlePresetConfig =
          ParticlePresetConfig
            { particlePresetConfigMaxParticles = Just 50.0,
              particlePresetConfigEmissionRate = Just 10.0,
              particlePresetConfigLifespan = Just 3.0,
              particlePresetConfigStartSize = Just 10.0,
              particlePresetConfigEndSize = Just 1.0,
              particlePresetConfigStartColor = Just "#ffffff",
              particlePresetConfigEndColor = Just "#0066ff",
              particlePresetConfigGravity = Just 0.0,
              particlePresetConfigTurbulenceStrength = Just 0.0,
              particlePresetConfigVelocitySpread = Just 5.0
            }
      }
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // built
-- ════════════════════════════════════════════════════════════════════════════

-- | Built-in path effect presets
--                                                                      // note
--                                                                      // note
builtInPathEffectPresets :: [PathEffectPreset]
builtInPathEffectPresets =
  [ PathEffectPreset
      { pathEffectPresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-path-sketch",
              presetMetadataName = "Sketchy",
              presetMetadataCategory = PresetCategoryPathEffect,
              presetMetadataDescription = Just "Hand-drawn sketch effect",
              presetMetadataTags = Just ["sketch", "hand-drawn", "rough"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        pathEffectPresetEffects = [] -- TODO: Use actual SplinePathEffectInstance when spline.ts is migrated
      },
    PathEffectPreset
      { pathEffectPresetMetadata =
          PresetMetadata
            { presetMetadataId = "builtin-path-wavy",
              presetMetadataName = "Wavy",
              presetMetadataCategory = PresetCategoryPathEffect,
              presetMetadataDescription = Just "Smooth wave deformation",
              presetMetadataTags = Just ["wave", "smooth", "organic"],
              presetMetadataAuthor = Nothing,
              presetMetadataCreatedAt = 0.0,
              presetMetadataUpdatedAt = 0.0,
              presetMetadataThumbnail = Nothing,
              presetMetadataIsBuiltIn = Just True,
              presetMetadataVersion = Nothing
            },
        pathEffectPresetEffects = [] -- TODO: Use actual SplinePathEffectInstance when spline.ts is migrated
      }
  ]
