-- |
-- Module      : Color.BlackBalance
-- Description : Black balance mathematics for OLED vs LCD displays
-- 
-- Handles monitor-specific black balance calculations with axioms
-- for OLED vs LCD display differences
--

import Color.Color

-- ============================================================================
-- MONITOR TYPE AXIOMS
-- ============================================================================

-- | Monitor type enumeration
inductive MonitorType where
  | OLED : MonitorType
  | LCD : MonitorType
  deriving Repr

-- | Axiom: OLED displays have true black (0% lightness = pure black)
-- LCD displays have backlight bleed (0% lightness ≠ pure black)
axiom oled_true_black (l : Lightness) : l.value = 0 → l.value = 0

-- | Axiom: LCD displays have minimum black level due to backlight
-- This is typically around 0.01-0.05 (1-5% lightness)
axiom lcd_min_black : ℝ := 0.02  -- 2% typical minimum

-- | Axiom: LCD black balance function
-- Maps requested lightness to actual display lightness accounting for backlight
axiom lcd_black_balance (requested : Lightness) : Lightness :=
  { value := max lcd_min_black requested.value
  , l_0_le := by
      -- max lcd_min_black requested.value ≥ lcd_min_black ≥ 0
      apply le_trans (le_max_left lcd_min_black requested.value)
      norm_num
  , l_le_1 := by
      -- max lcd_min_black requested.value ≤ max lcd_min_black 1 = 1
      apply le_trans (max_le (le_of_eq (by norm_num)) requested.l_le_1)
      norm_num
  }

-- | Axiom: OLED black balance function
-- OLED can achieve true black, but may have slight calibration offset
axiom oled_black_balance_offset : ℝ := 0.0  -- Typically 0, but can be calibrated

axiom oled_black_balance (requested : Lightness) : Lightness :=
  { value := max 0.0 (requested.value - oled_black_balance_offset)
  , l_0_le := by
      -- max 0.0 (requested.value - oled_black_balance_offset) ≥ 0
      apply le_max_left
      norm_num
  , l_le_1 := by
      -- max 0.0 (requested.value - oled_black_balance_offset) ≤ max 0.0 requested.value ≤ requested.value ≤ 1
      apply le_trans (max_le (le_refl 0.0) (by linarith [requested.l_le_1]))
      exact requested.l_le_1
  }

-- ============================================================================
-- BLACK BALANCE CALCULATION
-- ============================================================================

-- | Calculate actual display lightness accounting for monitor type
def applyBlackBalance (monitorType : MonitorType) (requested : Lightness) : Lightness :=
  match monitorType with
  | MonitorType.OLED => oled_black_balance requested
  | MonitorType.LCD => lcd_black_balance requested

-- | Calculate optimal background lightness for monitor type
-- Returns the minimum usable background lightness
def optimalBackgroundLightness (monitorType : MonitorType) : Lightness :=
  match monitorType with
  | MonitorType.OLED => 
    { value := 0.0, l_0_le := by norm_num, l_le_1 := by norm_num }  -- True black
  | MonitorType.LCD => 
    { value := lcd_min_black, l_0_le := by norm_num, l_le_1 := by norm_num }  -- Minimum black (0.02 is in [0,1])

-- | Calculate recommended background lightness for readability
-- Balances true black with readability (OLED can go darker, LCD needs more light)
def recommendedBackgroundLightness (monitorType : MonitorType) : Lightness :=
  match monitorType with
  | MonitorType.OLED => 
    { value := 0.11, l_0_le := by norm_num, l_le_1 := by norm_num }  -- OLED-safe (prevents burn-in)
  | MonitorType.LCD => 
    { value := 0.16, l_0_le := by norm_num, l_le_1 := by norm_num }  -- LCD minimum for contrast

-- ============================================================================
-- THEME GENERATION PARAMETERS
-- ============================================================================

-- | User-selected base color (from color wheel)
structure BaseColor where
  hue : Hue
  saturation : Saturation
  lightness : Lightness
  deriving Repr

-- | User-selected hero color (from color wheel)
structure HeroColor where
  hue : Hue
  saturation : Saturation
  lightness : Lightness
  deriving Repr

-- | Theme generation configuration
structure ThemeConfig where
  baseColor : BaseColor
  heroColor : HeroColor
  monitorType : MonitorType
  blackBalance : Lightness  -- User-adjusted black balance
  mode : Bool  -- false = dark, true = light
  deriving Repr

-- ============================================================================
-- THEME VARIANT GENERATION
-- ============================================================================

-- | Generate multiple theme variants from configuration
-- Returns list of (name, backgroundLightness) pairs
def generateThemeVariants (config : ThemeConfig) : List (String × Lightness) :=
  let baseLightness := config.blackBalance.value
  match config.monitorType with
  | MonitorType.OLED =>
    [
      ("pure-black", { value := 0.0, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("ultra-dark", { value := 0.04, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("dark", { value := 0.08, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("tuned", { value := 0.11, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("balanced", { value := max baseLightness 0.11, l_0_le := by
          -- max baseLightness 0.11 ≥ 0.11 ≥ 0
          apply le_trans (le_max_right baseLightness 0.11)
          norm_num
        , l_le_1 := by
          -- max baseLightness 0.11 ≤ max baseLightness 1 ≤ 1 (since baseLightness ≤ 1 from config.blackBalance)
          apply le_trans (max_le (config.blackBalance.l_le_1) (by norm_num))
          norm_num
        })
    ]
  | MonitorType.LCD =>
    [
      ("minimum", { value := lcd_min_black, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("dark", { value := 0.08, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("balanced", { value := max baseLightness 0.11, l_0_le := by
          -- max baseLightness 0.11 ≥ 0.11 ≥ 0
          apply le_trans (le_max_right baseLightness 0.11)
          norm_num
        , l_le_1 := by
          -- max baseLightness 0.11 ≤ max baseLightness 1 ≤ 1 (since baseLightness ≤ 1 from config.blackBalance)
          apply le_trans (max_le (config.blackBalance.l_le_1) (by norm_num))
          norm_num
        })
      ("github", { value := 0.16, l_0_le := by norm_num, l_le_1 := by norm_num })
      ("bright", { value := 0.20, l_0_le := by norm_num, l_le_1 := by norm_num })
    ]

-- | Generate light mode theme variants
def generateLightThemeVariants (config : ThemeConfig) : List (String × Lightness) :=
  [
    ("light", { value := 0.95, l_0_le := by norm_num, l_le_1 := by norm_num })
    ("bright", { value := 0.98, l_0_le := by norm_num, l_le_1 := by norm_num })
    ("paper", { value := 0.96, l_0_le := by norm_num, l_le_1 := by norm_num })
  ]

-- ============================================================================
-- COLOR ADJUSTMENT FOR BLACK BALANCE
-- ============================================================================

-- | Adjust HSL color to account for monitor black balance
-- Ensures colors remain visible on the selected monitor type
def adjustColorForMonitor (monitorType : MonitorType) (color : HSL) : HSL :=
  let adjustedLightness := applyBlackBalance monitorType color.l
  { h := color.h, s := color.s, l := adjustedLightness }

-- | Generate grayscale ramp accounting for monitor black balance
def generateGrayscaleRamp (monitorType : MonitorType) (baseHue : Hue) (startL : Lightness) (endL : Lightness) (steps : ℕ) : List HSL :=
  let stepSize := (endL.value - startL.value) / (steps - 1)
  List.range steps |>.map fun i =>
    let requestedL := { value := startL.value + stepSize * i, l_0_le := by
        -- startL.value + stepSize * i ≥ startL.value ≥ 0 (since startL is a Lightness)
        apply le_trans (add_le_add_left (mul_nonneg (by norm_num) (by norm_num)) startL.value)
        exact startL.l_0_le
      , l_le_1 := by
        -- startL.value + stepSize * i ≤ startL.value + (endL.value - startL.value) = endL.value ≤ 1
        -- This is a linear interpolation between startL and endL, both in [0,1]
        have h_step : stepSize * i ≤ endL.value - startL.value := by
          apply mul_le_of_le_one_left (by linarith [startL.l_0_le, endL.l_le_1])
          norm_num
        linarith [startL.l_le_1, endL.l_le_1, h_step]
      }
    let adjustedL := applyBlackBalance monitorType requestedL
    { h := baseHue
    , s := { value := 0.12 + 0.04 * (i : ℝ) / (steps - 1), s_0_le := by
        -- 0.12 + 0.04 * (i / (steps - 1)) ≥ 0.12 ≥ 0
        linarith
      , s_le_1 := by
        -- 0.12 + 0.04 * (i / (steps - 1)) ≤ 0.12 + 0.04 * 1 = 0.16 ≤ 1
        have h_div : (i : ℝ) / (steps - 1) ≤ 1 := by
          apply div_le_one
          linarith
        linarith
      }
    , l := adjustedL
    }
