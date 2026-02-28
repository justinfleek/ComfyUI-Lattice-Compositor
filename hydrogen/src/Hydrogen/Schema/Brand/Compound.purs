-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // brand // compound
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand Compound System — Token compositions for UI components.
-- |
-- | ## Architecture
-- |
-- | Brand Compounds bridge the gap between:
-- | - **Tokens**: Named values (color.primary.500, spacing.md, radius.lg)
-- | - **Element Compounds**: Rendering components that accept Schema atoms
-- |
-- | A Brand Compound defines "this component uses these tokens":
-- |
-- | ```
-- | ButtonCompound = {
-- |   background: "color.primary.500"
-- |   text: "color.on-primary"
-- |   radius: "radius.md"
-- |   paddingX: "spacing.4"
-- |   ...
-- | }
-- | ```
-- |
-- | ## Complete Component Coverage
-- |
-- | This module provides compounds for EVERY UI component:
-- |
-- | **Interactive:**
-- | - Button, IconButton, Link, Toggle, Switch
-- | - Checkbox, Radio, Select, Slider
-- |
-- | **Containers:**
-- | - Card, Alert, Modal, Dialog, Sheet
-- | - Accordion, Collapsible, Tabs
-- |
-- | **Data Display:**
-- | - Badge, Avatar, Tag, Chip
-- | - Table, DataGrid, List
-- | - Tooltip, Popover
-- |
-- | **Form:**
-- | - Input, Textarea, SearchInput
-- | - DatePicker, TimePicker, ColorPicker
-- | - NumberInput, PhoneInput, OTPInput
-- |
-- | **Feedback:**
-- | - Toast, Alert, Progress, Skeleton
-- | - Spinner, LoadingBar
-- |
-- | **Navigation:**
-- | - Breadcrumb, Tabs, Menu, Sidebar
-- | - Pagination, Stepper
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When Agent A composes a form with buttons, inputs, and cards, they reference
-- | compound styles by semantic name. Agent B rendering the same form gets
-- | identical visual output because both resolve through the same compound
-- | definitions.
-- |
-- | Compounds are pure data. No side effects. No ambiguity. Same compounds,
-- | same output — guaranteed.

module Hydrogen.Schema.Brand.Compound
  ( -- * Re-exports
    module Hydrogen.Schema.Brand.Compound.Types
  ) where

import Hydrogen.Schema.Brand.Compound.Types
