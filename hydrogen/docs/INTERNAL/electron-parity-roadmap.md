# Electron Parity Roadmap

> EVERYTHING. Norman Stansfield energy.

## Status: ANALYSIS PHASE — Cataloging Electron features for pure replacement

---

## Philosophy

Electron is a **legacy runtime** — a JavaScript/Chromium wrapper that bundles a browser
into a "native" app. It's everything wrong with modern software:

- 200MB+ app bundles for a text editor
- Multiple copies of Chromium eating RAM
- JavaScript runtime overhead
- No type safety at the system boundary
- Security model held together with duct tape

**Hydrogen's approach:** Pure data that can be interpreted by any runtime.

The goal is NOT "Electron but in PureScript." The goal is:

1. **Define desktop app capabilities as Schema atoms** — Window, Menu, Tray, Dialog, etc.
2. **Generate interpreters** for native runtimes (Tauri/Rust, Wails/Go, or pure WASM)
3. **Zero JavaScript** at runtime — the interpreter is native code reading pure Element data

---

## ELECTRON FEATURE AUDIT

Every Electron API, cataloged for replacement.

### 1. Window Management

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `BrowserWindow` | `Schema/Desktop/Window.purs` | ❌ NOT STARTED |
| `new BrowserWindow(options)` | `Window { size, position, frame, ... }` | ❌ |
| `win.show()` / `win.hide()` | `WindowVisibility` atom | ❌ |
| `win.minimize()` / `win.maximize()` | `WindowState` atom | ❌ |
| `win.setFullScreen()` | `FullscreenMode` atom | ❌ |
| `win.setBounds()` | `WindowBounds` (uses Dimension atoms) | ❌ |
| `win.setTitle()` | Title is Element content | ❌ |
| `win.setIcon()` | `WindowIcon` (uses existing Icon schema) | ❌ |
| `win.setMenu()` | `WindowMenu` (see Menu section) | ❌ |
| `win.setAlwaysOnTop()` | `WindowLayer` atom | ❌ |
| `win.setOpacity()` | Uses existing `Opacity` from Color | ✅ ATOM EXISTS |
| `win.setBackgroundColor()` | Uses existing Color schema | ✅ ATOM EXISTS |
| `win.webContents` | N/A — no web contents, pure Element | N/A |
| `win.loadURL()` | N/A — no URLs, Element is the content | N/A |

**New atoms needed:**
- `WindowId` — Unique window identifier
- `WindowState` — Normal, Minimized, Maximized, Fullscreen
- `WindowVisibility` — Visible, Hidden
- `WindowFrame` — Framed, Frameless, Transparent
- `WindowBounds` — Position + Size (uses existing Dimension atoms)
- `WindowLayer` — Normal, AlwaysOnTop, AlwaysOnBottom
- `WindowResizable` — Boolean atom
- `WindowMovable` — Boolean atom
- `WindowMinSize` / `WindowMaxSize` — Size constraints

### 2. Menu System

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `Menu` | `Schema/Desktop/Menu.purs` | ❌ NOT STARTED |
| `Menu.buildFromTemplate()` | `Menu` compound from atoms | ❌ |
| `MenuItem` | `MenuItem` atom | ❌ |
| `MenuItem.click` | `MenuAction msg` | ❌ |
| `MenuItem.role` | `MenuRole` atom | ❌ |
| `MenuItem.type` | `MenuItemType` atom | ❌ |
| `MenuItem.label` | Uses existing Text | ✅ EXISTS |
| `MenuItem.accelerator` | `KeyboardShortcut` (uses Gestural/Keyboard) | ✅ PARTIAL |
| `MenuItem.icon` | Uses existing Icon schema | ✅ EXISTS |
| `MenuItem.submenu` | Recursive `Menu` | ❌ |
| `Menu.popup()` | Context menu trigger (uses Gestural) | ✅ PARTIAL |

**New atoms needed:**
- `MenuId` — Unique menu identifier
- `MenuItemType` — Normal, Separator, Submenu, Checkbox, Radio
- `MenuRole` — Undo, Redo, Cut, Copy, Paste, SelectAll, Quit, etc.
- `MenuPosition` — Application menu, Context menu, Tray menu

### 3. System Tray

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `Tray` | `Schema/Desktop/Tray.purs` | ❌ NOT STARTED |
| `new Tray(icon)` | `TrayIcon` (uses Icon schema) | ❌ |
| `tray.setTitle()` | `TrayTitle` atom | ❌ |
| `tray.setToolTip()` | `TrayTooltip` atom | ❌ |
| `tray.setContextMenu()` | `TrayMenu` (uses Menu schema) | ❌ |
| `tray.on('click')` | `TrayAction msg` | ❌ |

**New atoms needed:**
- `TrayId` — Unique tray identifier
- `TrayTitle` — macOS menu bar title
- `TrayTooltip` — Hover tooltip

### 4. Dialogs

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `dialog.showOpenDialog()` | `Schema/Desktop/Dialog.purs` | ❌ NOT STARTED |
| `dialog.showSaveDialog()` | `SaveDialog` compound | ❌ |
| `dialog.showMessageBox()` | `MessageDialog` compound | ❌ |
| `dialog.showErrorBox()` | `ErrorDialog` compound | ❌ |
| File filters | `FileFilter` atom | ❌ |
| Default path | Uses existing path types | ❌ |

**New atoms needed:**
- `DialogId` — Unique dialog identifier
- `DialogType` — Open, Save, Message, Error
- `DialogButtons` — OK, Cancel, Yes, No, etc.
- `DialogIcon` — None, Info, Warning, Error, Question
- `FileFilter` — Extensions + description
- `DialogResult` — User selection

### 5. Notifications

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `Notification` | `Schema/Desktop/Notification.purs` | ❌ NOT STARTED |
| `new Notification(options)` | `Notification` compound | ❌ |
| `notification.show()` | Notification visibility | ❌ |
| `notification.close()` | Notification lifecycle | ❌ |
| `notification.on('click')` | `NotificationAction msg` | ❌ |

**New atoms needed:**
- `NotificationId` — Unique notification identifier
- `NotificationUrgency` — Low, Normal, Critical
- `NotificationTimeout` — Auto-dismiss duration

### 6. Clipboard

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `clipboard.readText()` | `Schema/Desktop/Clipboard.purs` | ❌ NOT STARTED |
| `clipboard.writeText()` | `ClipboardText` | ❌ |
| `clipboard.readHTML()` | `ClipboardHTML` | ❌ |
| `clipboard.readImage()` | `ClipboardImage` | ❌ |
| `clipboard.readRTF()` | `ClipboardRTF` | ❌ |
| `clipboard.clear()` | Clipboard command | ❌ |

**Note:** Clipboard operations are EFFECTS, not pure data. They need to be:
1. Defined as `Cmd` types in the runtime
2. Interpreter executes them against native clipboard

### 7. Shell Integration

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `shell.openExternal()` | `Schema/Desktop/Shell.purs` | ❌ NOT STARTED |
| `shell.openPath()` | `OpenPath` command | ❌ |
| `shell.showItemInFolder()` | `RevealInFolder` command | ❌ |
| `shell.beep()` | Uses existing Haptic/Audio | ✅ EXISTS |
| `shell.moveItemToTrash()` | `MoveToTrash` command | ❌ |

### 8. Native File System

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `fs` (Node.js) | `Schema/Desktop/FileSystem.purs` | ❌ NOT STARTED |
| File read/write | `FileOperation` commands | ❌ |
| Watch files | `FileWatcher` | ❌ |
| Path operations | `FilePath` atoms | ❌ |

**Note:** File system access is sandboxed differently per platform.
Need to define capability model.

### 9. App Lifecycle

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `app.quit()` | `Schema/Desktop/App.purs` | ❌ NOT STARTED |
| `app.relaunch()` | `AppCommand` | ❌ |
| `app.isReady` | `AppState` atom | ❌ |
| `app.getPath()` | `AppPath` atoms | ❌ |
| `app.getVersion()` | `AppVersion` atom | ❌ |
| `app.setName()` | `AppName` atom | ❌ |
| `app.on('ready')` | App lifecycle events | ❌ |
| `app.on('window-all-closed')` | App lifecycle events | ❌ |
| `app.on('before-quit')` | App lifecycle events | ❌ |

**New atoms needed:**
- `AppId` — Application identifier
- `AppState` — Starting, Ready, Quitting
- `AppPath` — Home, AppData, Temp, Documents, etc.

### 10. IPC (Inter-Process Communication)

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `ipcMain` / `ipcRenderer` | N/A — no processes | N/A |

**Note:** Electron's IPC exists because of the process split (main vs renderer).
Hydrogen has no processes — it's pure data. The interpreter runs in a single
native process. Message passing between windows uses the standard `Msg` system.

### 11. Protocol Handlers

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `protocol.registerHttpProtocol()` | `Schema/Desktop/Protocol.purs` | ❌ NOT STARTED |
| Custom URL schemes | `CustomScheme` atom | ❌ |
| Deep linking | `DeepLink` handler | ❌ |

### 12. Auto-Updater

| Electron API | Hydrogen Schema | Status |
|--------------|-----------------|--------|
| `autoUpdater` | `Schema/Desktop/Update.purs` | ❌ NOT STARTED |
| Check for updates | `UpdateCheck` command | ❌ |
| Download update | `UpdateDownload` command | ❌ |
| Install update | `UpdateInstall` command | ❌ |
| Update progress | Uses existing `Progress` atom | ✅ EXISTS |

---

## NATIVE RUNTIME OPTIONS

Hydrogen Element can be interpreted by:

### Option 1: Tauri (Rust)

**Pros:**
- ~600KB binary vs 200MB Electron
- Rust type safety
- Native webview (not bundled Chromium)
- Strong security model

**Cons:**
- Still uses webview for UI
- Rust FFI complexity

### Option 2: Wails (Go)

**Pros:**
- Simple Go backend
- Native webview
- Cross-platform

**Cons:**
- Go's type system less expressive
- Still uses webview

### Option 3: Pure WASM + Native Canvas

**Pros:**
- Zero webview
- Element rendered directly to native canvas/GPU
- Maximum performance
- True native feel

**Cons:**
- Most work to implement
- Platform-specific windowing code needed

### Option 4: SDL2/GLFW + WebGPU

**Pros:**
- Battle-tested windowing
- WebGPU for rendering
- Cross-platform
- No browser dependency

**Cons:**
- Need to handle input, accessibility ourselves

**Recommended:** Start with Tauri for quick wins, migrate to pure WASM+WebGPU long term.

---

## IMPLEMENTATION PHASES

### Phase 1: Desktop Schema Types

Create `src/Hydrogen/Schema/Desktop/` with:
- Window.purs — Window atoms
- Menu.purs — Menu atoms
- Tray.purs — System tray atoms
- Dialog.purs — Dialog atoms
- Notification.purs — Notification atoms
- Clipboard.purs — Clipboard types
- Shell.purs — Shell integration
- App.purs — App lifecycle
- FileSystem.purs — File system types (sandboxed)

### Phase 2: Desktop Element Extension

Extend Element to include desktop primitives:
```purescript
data Element msg
  = ...existing...
  | DesktopWindow (Window msg) (Array (Element msg))
  | DesktopMenu (Menu msg)
  | DesktopTray (Tray msg)
  | DesktopDialog (Dialog msg)
  | DesktopNotification (Notification msg)
```

### Phase 3: Tauri Interpreter

Create Tauri backend that:
1. Reads Element data
2. Creates native windows via Tauri
3. Routes events back as Msg
4. Handles Cmd effects (clipboard, file system, etc.)

### Phase 4: Pure WebGPU Interpreter

Replace webview with direct WebGPU rendering:
1. SDL2/GLFW for windowing
2. WebGPU for Element → pixels
3. Platform accessibility APIs
4. Native file dialogs

---

## ATOMS SUMMARY

**New Desktop atoms needed:** ~45

| Module | Atoms |
|--------|-------|
| Window | WindowId, WindowState, WindowVisibility, WindowFrame, WindowBounds, WindowLayer, WindowResizable, WindowMovable, WindowMinSize, WindowMaxSize |
| Menu | MenuId, MenuItemType, MenuRole, MenuPosition |
| Tray | TrayId, TrayTitle, TrayTooltip |
| Dialog | DialogId, DialogType, DialogButtons, DialogIcon, FileFilter, DialogResult |
| Notification | NotificationId, NotificationUrgency, NotificationTimeout |
| Clipboard | ClipboardFormat (text, html, image, rtf) |
| Shell | ShellCommand |
| App | AppId, AppState, AppPath |
| Protocol | CustomScheme, DeepLink |
| Update | UpdateState, UpdateChannel |

**Existing atoms that apply:** ~20+
- Dimension atoms (Pixel, Size2D, etc.) for window bounds
- Color atoms for window backgrounds
- Icon atoms for window/tray icons
- Gestural/Keyboard for accelerators
- Haptic/Audio for system sounds
- Progress for update progress

---

## ELECTRON FEATURES WE WILL NOT REPLICATE

These are Electron-specific hacks we don't need:

| Feature | Why Not |
|---------|---------|
| `webContents` | No web content — Element IS the content |
| `session` | No browser sessions |
| `cookies` | No cookies — use proper auth |
| `webFrame` | No frames |
| `webRequest` | No web requests from UI — API layer handles this |
| `desktopCapturer` | Screen capture is a separate capability |
| `powerMonitor` | Platform-specific, rarely needed |
| `powerSaveBlocker` | Platform-specific |
| `systemPreferences` | Read via App atoms |
| `TouchBar` | macOS-specific, low priority |
| `Debugger` | DevTools not needed — Element is inspectable data |

---

## PRIORITY ORDER

1. **Window + Menu** — Core desktop app structure
2. **Dialog** — File open/save is critical
3. **Tray + Notification** — Background app support
4. **Clipboard** — Copy/paste
5. **App lifecycle** — Quit, restart, paths
6. **Shell** — Open URLs, reveal files
7. **FileSystem** — Sandboxed file access
8. **Protocol** — Deep linking
9. **Update** — Auto-update

---

*Created: 2026-02-26*
*EVERYONE.*
