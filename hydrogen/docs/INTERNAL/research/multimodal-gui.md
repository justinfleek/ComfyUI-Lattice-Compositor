# A Multimodal GUI Architecture for Interfacing with LLM-Based Conversational Assistants

**arXiv:** 2510.06223  
**Authors:** Hans G.W. van Dam (uxx.ai)  
**Status:** IN_PROGRESS

---

## 1. Abstract

Architecture enabling GUIs to interface with LLM-based speech-enabled assistants via Model Context Protocol (MCP). Key features:
- Application's navigation graph exposed through MCP
- ViewModel exposes tools for current view
- Full voice accessibility
- Reliable alignment between spoken input and visual interface
- Future-proofs for OS super assistants

---

## 2. Architecture Overview

### 2.1 Core Components

```
┌─────────────────────────────────────────────────────────┐
│                    Multimodal GUI                        │
├─────────────────────────────────────────────────────────┤
│                                                          │
│  ┌─────────┐    ┌─────────────┐    ┌───────────────┐ │
│  │   GUI    │◀───│  ViewModel   │◀───│  Model Context │ │
│  │  (View)  │    │   (State)   │    │   Protocol    │ │
│  └─────────┘    └──────┬──────┘    └───────┬───────┘ │
│                          │                    │          │
│                          ▼                    ▼          │
│                   ┌─────────────────────────────┐        │
│                   │    LLM Assistant           │        │
│                   │  (Voice + Function Calls)   │        │
│                   └─────────────────────────────┘        │
└─────────────────────────────────────────────────────────┘
```

### 2.2 MCP Integration

**Model Context Protocol (MCP):**
- Exposes application navigation graph
- Provides tool definitions
- Enables semantic understanding

---

## 3. Key Design Principles

### 3.1 Voice-Driven Requirements

| Requirement | Description |
|------------|-------------|
| Comprehensive coverage | All GUI actions via voice |
| Accurate mapping | Spoken requests → application actions |
| Real-time STT | Speech-to-text or direct audio interpretation |
| Multimodal feedback | GUI + TTS synchronized |
| Repair capability | Handle self/other corrections |

### 3.2 ViewModel Tool Exposure

```typescript
interface ViewModel {
  // Tools for currently visible view
  getLocalTools(): Tool[];
  
  // Application-global tools from GUI tree
  getGlobalTools(): Tool[];
  
  // Navigation graph
  getNavigationGraph(): Graph;
}
```

---

## 4. GUI Strengths vs Speech

### 4.1 GUI Strengths

- Fast visual scanning
- Direct and precise control
- Immediate visual feedback
- Easy discoverability
- Muscle memory support
- Efficient multitasking

### 4.2 Speech Complementarities

- Natural interaction
- Accessibility (hands/eyes busy)
- Complex/unknown navigation
- Multitasking scenarios

---

## 5. Privacy & Deployment

### 5.1 Local Open-Weight Models

Evaluation findings:
- Recent smaller open-weight models approach proprietary performance
- Enterprise-grade hardware needed for responsiveness
- Privacy benefits of local deployment

### 5.2 Architecture Benefits

- Explicit semantics enable accurate assistant responses
- Standardized MCP for interoperability
- Dualistic OS assistants (visual + semantic)

---

## 6. Key Definitions

1. **MCP:** Model Context Protocol - standardized way to expose app semantics
2. **MVVM:** Model-View-ViewModel pattern
3. **CUA:** Computer Use Agent
4. **STT:** Speech-to-Text
5. **TTS:** Text-to-Speech

---

## 7. Relation to Hydrogen

```purescript
-- Multimodal UI types
data UIComponent
  = Button Text | Input Field | Slider Value | NavigationItem

data ViewState
  = ViewState
      { visibleComponents :: Array UIComponent
      , availableTools :: Array Tool
      , navigationGraph :: Graph
      }

-- Voice interaction
voiceCommand ::
  Audio ->
  LLM ->
  (Action, ViewState)

-- Tool execution
executeTool ::
  Tool ->
  ViewState ->
  (Result, ViewState)
```

---

## 8. Bibliography

1. van Dam "A Multimodal GUI Architecture for Interfacing with LLM-Based Conversational Assistants" 2025
2. MCP Specification

---

*Document generated: 2026-02-26*
