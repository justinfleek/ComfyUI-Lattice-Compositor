# Straylight Protocol Enforcement Flowchart

**Visual representation of the complete enforcement flow**

## Main Flowchart (Mermaid)

```mermaid
flowchart TD
    Start([User Request]) --> AI[AI Assistant Reads Config]
    
    AI --> Rules1[.cursor/rules/001_straylight-protocol.mdc]
    AI --> Rules2[.cursor/rules/002_validation-required.mdc]
    AI --> Rules3[.cursor/rules/003_mandatory-workflow.mdc]
    AI --> Agents[AGENTS.md]
    AI --> Claude[CLAUDE.md]
    
    Rules1 --> MCP[MCP Server Connection]
    Rules2 --> MCP
    Rules3 --> MCP
    Agents --> MCP
    Claude --> MCP
    
    MCP --> Plan[Step 1: straylight_plan]
    Plan --> Locate[Step 2: straylight_locate]
    Locate --> Template[Step 3: straylight_template]
    Template --> Generate[Step 4: Generate Code]
    
    Generate --> Validate[Step 5: straylight_validate]
    Validate -->|Invalid| Fix[Fix Errors]
    Fix --> Validate
    Validate -->|Valid| Write[Write Code to File]
    
    Write --> Watcher{File Watcher<br/>Running?}
    Watcher -->|Yes| WatchVal[watch-and-validate.js<br/>Validates on Save]
    Watcher -->|No| Commit
    WatchVal -->|Violations| WatchErr[Show Errors]
    WatchVal -->|Clean| Commit
    
    Commit[User: git commit] --> PreCommit[hooks/pre-commit]
    PreCommit --> PreVal[validate-file.js<br/>Validates All Files]
    
    PreVal -->|Violations| BlockCommit[❌ Block Commit]
    PreVal -->|Clean| AllowCommit[✅ Allow Commit]
    
    BlockCommit --> FixCommit[User Must Fix]
    FixCommit --> Commit
    
    AllowCommit --> Push[User: git push]
    Push --> CI[.github/workflows/straylight-enforcement.yml]
    
    CI --> CIVal1[Validate MCP Syntax]
    CI --> CIVal2[Run Nix Lint]
    CI --> CIVal3[Check Protocol Violations]
    CI --> CIVal4[Validate Changed Files]
    CI --> CIVal5[Check File Sizes]
    CI --> CIVal6[Check Literate Programming]
    
    CIVal1 --> CIResult{Violations?}
    CIVal2 --> CIResult
    CIVal3 --> CIResult
    CIVal4 --> CIResult
    CIVal5 --> CIResult
    CIVal6 --> CIResult
    
    CIResult -->|Yes| BlockMerge[❌ CI Fails<br/>Block Merge]
    CIResult -->|No| AllowMerge[✅ CI Passes<br/>Allow Merge]
    
    BlockMerge --> FixCI[User Must Fix]
    FixCI --> Push
    
    AllowMerge --> Production([✅ Code in Production])
    
    style Start fill:#e1f5ff
    style Production fill:#d4edda
    style BlockCommit fill:#f8d7da
    style BlockMerge fill:#f8d7da
    style Validate fill:#fff3cd
    style PreVal fill:#fff3cd
    style CIVal4 fill:#fff3cd
```

## Detailed Validation Flow

```mermaid
flowchart LR
    Code[Generated Code] --> Validate{straylight_validate}
    
    Validate --> CheckSize{File Size<br/>>500 lines?}
    CheckSize -->|Yes| SizeErr[❌ STRAYLIGHT-010 Error]
    CheckSize -->|No| CheckForbidden{Forbidden<br/>Rules}
    
    CheckForbidden --> Forbidden1[WSN-E001: with lib;]
    CheckForbidden --> Forbidden2[WSN-E002: rec in derivation]
    CheckForbidden --> Forbidden3[WSN-E003: camelCase]
    CheckForbidden --> Forbidden4[WSN-E004: Missing _class]
    CheckForbidden --> Forbidden5[WSN-E005: IFD]
    CheckForbidden --> Forbidden6[WSN-E006: Heredocs]
    CheckForbidden --> Forbidden7[WSN-E007: nixpkgs.config]
    CheckForbidden --> Forbidden8[WSN-E008: Missing meta]
    CheckForbidden --> Forbidden9[WSN-E009: Missing description]
    CheckForbidden --> Forbidden10[WSN-E010: Missing mainProgram]
    CheckForbidden --> Forbidden11[STRAYLIGHT-004: Missing import]
    CheckForbidden --> Forbidden12[STRAYLIGHT-011: Literate violations]
    
    Forbidden1 --> CheckRequired{Required<br/>Rules}
    Forbidden2 --> CheckRequired
    Forbidden3 --> CheckRequired
    Forbidden4 --> CheckRequired
    Forbidden5 --> CheckRequired
    Forbidden6 --> CheckRequired
    Forbidden7 --> CheckRequired
    Forbidden8 --> CheckRequired
    Forbidden9 --> CheckRequired
    Forbidden10 --> CheckRequired
    Forbidden11 --> CheckRequired
    Forbidden12 --> CheckRequired
    
    CheckRequired --> Required1[STRAYLIGHT-004: Script imports]
    CheckRequired --> Required2[WSN-E004: Module _class]
    
    Required1 --> CheckWarnings{Warning<br/>Rules}
    Required2 --> CheckWarnings
    
    CheckWarnings --> Warning1[WSN-W001: Long lines]
    CheckWarnings --> Warning2[WSN-W002: Missing description]
    CheckWarnings --> Warning3[WSN-W003: Long strings]
    CheckWarnings --> Warning4[WSN-W004: Missing meta]
    CheckWarnings --> Warning5[WSN-W005: Missing description]
    CheckWarnings --> Warning6[WSN-W006: Missing license]
    CheckWarnings --> Warning7[WSN-W007: Missing mainProgram]
    
    Warning1 --> Result{Any Errors?}
    Warning2 --> Result
    Warning3 --> Result
    Warning4 --> Result
    Warning5 --> Result
    Warning6 --> Result
    Warning7 --> Result
    SizeErr --> Result
    
    Result -->|Yes| ReturnErr[Return: valid=false<br/>errors=[...]]
    Result -->|No| ReturnOk[Return: valid=true<br/>errors=[]]
    
    style Validate fill:#fff3cd
    style Result fill:#d4edda
    style ReturnErr fill:#f8d7da
    style ReturnOk fill:#d4edda
```

## Component Interaction Diagram

```mermaid
graph TB
    subgraph "User Layer"
        User[User Request]
    end
    
    subgraph "AI Assistant Layer"
        Cursor[Cursor/Claude/Windsurf/Cline]
        Rules[.cursor/rules/*.mdc]
        Configs[AGENTS.md, CLAUDE.md, etc.]
    end
    
    subgraph "MCP Layer"
        MCPServer[.claude/straylight-mcp.js]
        MCPSettings[.claude/settings.json]
        Tools[straylight_validate<br/>straylight_template<br/>straylight_locate<br/>straylight_plan]
    end
    
    subgraph "Validation Layer"
        ValidateFile[scripts/validate-file.js]
        TestSuite[scripts/test-all-violations.js]
        Watcher[scripts/watch-and-validate.js]
    end
    
    subgraph "Git Layer"
        PreCommit[hooks/pre-commit]
        Git[Git Repository]
    end
    
    subgraph "CI/CD Layer"
        CIWorkflow[.github/workflows/straylight-enforcement.yml]
        CDWorkflow[.github/workflows/cd.yml]
        GitHub[GitHub Actions]
    end
    
    subgraph "Rule Source"
        RulesObject[RULES Object<br/>56+ Rules]
        ProtocolDocs[straylight-protocol/docs/rfc/*.md]
    end
    
    User --> Cursor
    Cursor --> Rules
    Cursor --> Configs
    Cursor --> MCPServer
    MCPServer --> MCPSettings
    MCPServer --> Tools
    MCPServer --> RulesObject
    MCPServer --> ProtocolDocs
    
    Tools --> ValidateFile
    ValidateFile --> RulesObject
    TestSuite --> ValidateFile
    Watcher --> ValidateFile
    
    Cursor --> Git
    Git --> PreCommit
    PreCommit --> ValidateFile
    
    Git --> GitHub
    GitHub --> CIWorkflow
    GitHub --> CDWorkflow
    CIWorkflow --> ValidateFile
    CDWorkflow --> ValidateFile
    
    style RulesObject fill:#fff3cd
    style MCPServer fill:#d1ecf1
    style ValidateFile fill:#d4edda
    style CIWorkflow fill:#f8d7da
```

## Scope Graph: Dependencies

```mermaid
graph LR
    subgraph "Source of Truth"
        RULES[RULES Object<br/>.claude/straylight-mcp.js]
    end
    
    subgraph "Consumers"
        MCP[MCP Server<br/>straylight-mcp.js]
        Val[validate-file.js]
        Hook[pre-commit hook]
        CI[CI Workflow]
        Watch[File Watcher]
    end
    
    subgraph "Configuration"
        CursorRules[.cursor/rules/*.mdc]
        Agents[AGENTS.md]
        Claude[CLAUDE.md]
        Settings[.claude/settings.json]
    end
    
    subgraph "Documentation"
        RFCs[straylight-protocol/docs/rfc/*.md]
        Contrib[CONTRIBUTING.md]
        Skill[skill/straylight-script/SKILL.md]
    end
    
    RULES --> MCP
    RULES --> Val
    Val --> Hook
    Val --> CI
    Val --> Watch
    
    CursorRules --> MCP
    Agents --> MCP
    Claude --> MCP
    Settings --> MCP
    
    RFCs --> MCP
    Contrib --> MCP
    Skill --> MCP
    
    style RULES fill:#ffd700
    style MCP fill:#87ceeb
    style Val fill:#90ee90
```

## Enforcement Points Timeline

```mermaid
gantt
    title Straylight Protocol Enforcement Timeline
    dateFormat X
    axisFormat %s
    
    section AI Generation
    Read Rules           :0, 1
    Call straylight_plan      :1, 1
    Call straylight_locate    :2, 1
    Call straylight_template  :3, 1
    Generate Code        :4, 2
    Validate (MCP)       :6, 2
    Fix Errors           :8, 2
    Write File           :10, 1
    
    section File System
    File Saved           :11, 1
    Watcher Validates    :11, 1
    
    section Git Operations
    git add              :12, 1
    git commit           :13, 1
    Pre-commit Hook      :13, 1
    Commit Allowed       :14, 1
    git push             :15, 1
    
    section CI/CD
    CI Triggered         :16, 1
    CI Validation        :16, 3
    CI Passes            :19, 1
    Merge Allowed        :20, 1
```

## Rule Application Sequence

```mermaid
sequenceDiagram
    participant U as User
    participant AI as AI Assistant
    participant MCP as MCP Server
    participant R as RULES Object
    participant F as File System
    participant G as Git
    participant H as Pre-commit Hook
    participant C as CI Workflow
    
    U->>AI: "Create package my-tool"
    AI->>MCP: straylight_plan({ task: "..." })
    MCP->>R: Lookup rules
    R-->>MCP: Return docs
    MCP-->>AI: Return plan
    
    AI->>MCP: straylight_locate({ type: "package" })
    MCP-->>AI: Return path
    
    AI->>MCP: straylight_template({ type: "package" })
    MCP-->>AI: Return template
    
    AI->>AI: Generate code
    
    AI->>MCP: straylight_validate({ code: "...", type: "nix" })
    MCP->>R: Check all rules
    R-->>MCP: Return violations
    MCP-->>AI: { valid: false, errors: [...] }
    
    AI->>AI: Fix errors
    AI->>MCP: straylight_validate({ code: fixed, type: "nix" })
    MCP->>R: Check all rules
    R-->>MCP: No violations
    MCP-->>AI: { valid: true, errors: [] }
    
    AI->>F: Write file
    
    U->>G: git commit
    G->>H: Trigger pre-commit
    H->>R: Validate files
    R-->>H: All clean
    H-->>G: Allow commit
    
    U->>G: git push
    G->>C: Trigger CI
    C->>R: Validate changed files
    R-->>C: All clean
    C-->>G: CI passes
    G-->>U: Merge allowed
```

## Simplified Quick Reference

```
┌─────────────────────────────────────────────────────────────┐
│              STRAYLIGHT PROTOCOL ENFORCEMENT FLOW                 │
└─────────────────────────────────────────────────────────────┘

USER REQUEST
    │
    ▼
AI ASSISTANT
    ├─→ Reads: Rules, Configs, AGENTS.md
    ├─→ Calls: MCP Tools (plan, locate, template)
    ├─→ Generates: Code
    └─→ Validates: straylight_validate (MCP tool)
         │
         ├─→ ❌ Violations → Fix → Re-validate
         │
         └─→ ✅ Valid → Write File
              │
              ▼
FILE SAVED
    │
    ├─→ Optional: File Watcher validates
    │
    └─→ Git Commit
         │
         └─→ Pre-commit Hook validates
              │
              ├─→ ❌ Violations → Block commit
              │
              └─→ ✅ Clean → Allow commit
                   │
                   └─→ Git Push
                        │
                        └─→ CI Workflow validates
                             │
                             ├─→ ❌ Violations → Block merge
                             │
                             └─→ ✅ Clean → Allow merge
                                  │
                                  └─→ ✅ PRODUCTION

ENFORCEMENT POINTS:
1. AI Generation (MCP validation) - 100% coverage
2. File Save (Watcher) - Optional
3. Git Commit (Pre-commit hook) - 100% coverage
4. Git Push (CI workflow) - 100% coverage

RULE SOURCE:
Single source of truth: RULES object in .claude/straylight-mcp.js
All validators use same rules (synchronized)
```
