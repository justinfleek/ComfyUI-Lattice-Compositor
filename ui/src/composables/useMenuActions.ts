/**
 * Menu Actions Composable
 *
 * Handles all menu bar action dispatching for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { useHistoryStore } from "@/stores/historyStore";

export interface MenuActionsOptions {
  // Dialog refs
  showExportDialog: Ref<boolean>;
  showPrecomposeDialog: Ref<boolean>;
  showTimeStretchDialog: Ref<boolean>;
  showPreferencesDialog: Ref<boolean>;
  showHDPreview: Ref<boolean>;

  // Tab refs
  leftTab: Ref<"project" | "effects" | "assets">;
  aiTab: Ref<"chat" | "generate" | "flow" | "decompose">;
  viewZoom: Ref<string>;
  showCurveEditor: Ref<boolean>;

  // Panel visibility
  expandedPanels: Ref<{
    properties: boolean;
    camera: boolean;
    audio: boolean;
    renderQueue: boolean;
    align: boolean;
    physics: boolean;
    styles: boolean;
  }>;

  // Callbacks
  triggerAssetImport: () => void;
  triggerProjectOpen: () => void;
  handleZoomChange: () => void;
}

export function useMenuActions(options: MenuActionsOptions) {
  // Cast to any because Pinia store actions are spread from external modules
  // and TypeScript can't infer their types correctly
  const store = useCompositorStore() as any;
  const _historyStore = useHistoryStore();

  const {
    showExportDialog,
    showPrecomposeDialog,
    showTimeStretchDialog,
    showPreferencesDialog,
    showHDPreview,
    leftTab,
    aiTab,
    viewZoom,
    showCurveEditor,
    expandedPanels,
    triggerAssetImport,
    triggerProjectOpen,
    handleZoomChange,
  } = options;

  function handleZoomIn() {
    const levels = ["25", "50", "75", "100", "150", "200"];
    const currentIndex = levels.indexOf(viewZoom.value);
    if (currentIndex < levels.length - 1 && currentIndex >= 0) {
      viewZoom.value = levels[currentIndex + 1];
      handleZoomChange();
    } else if (viewZoom.value === "fit") {
      viewZoom.value = "100";
      handleZoomChange();
    }
  }

  function handleZoomOut() {
    const levels = ["25", "50", "75", "100", "150", "200"];
    const currentIndex = levels.indexOf(viewZoom.value);
    if (currentIndex > 0) {
      viewZoom.value = levels[currentIndex - 1];
      handleZoomChange();
    }
  }

  /**
   * Handle actions from the menu bar
   */
  function handleMenuAction(action: string) {
    switch (action) {
      // File menu
      case "newProject":
        if (confirm("Create a new project? Unsaved changes will be lost.")) {
          store.newProject();
        }
        break;
      case "openProject":
        triggerProjectOpen();
        break;
      case "saveProject":
        store.saveProject();
        break;
      case "saveProjectAs":
        store.saveProjectAs();
        break;
      case "import":
        triggerAssetImport();
        break;
      case "export":
        showExportDialog.value = true;
        break;

      // Edit menu
      case "undo":
        store.undo();
        break;
      case "redo":
        store.redo();
        break;
      case "cut":
        store.cutSelected();
        break;
      case "copy":
        store.copySelected();
        break;
      case "paste":
        store.paste();
        break;
      case "duplicate":
        store.duplicateSelectedLayers();
        break;
      case "delete":
        store.deleteSelectedLayers();
        break;
      case "selectAll":
        store.selectAllLayers();
        break;
      case "deselectAll":
        store.clearSelection();
        break;

      // Create menu - layer types
      case "createSolid":
        store.createLayer("solid");
        break;
      case "createText":
        store.createLayer("text");
        break;
      case "createShape":
        store.createLayer("spline");
        break;
      case "createPath":
        store.createLayer("path");
        break;
      case "createCamera":
        store.createLayer("camera");
        break;
      case "createLight":
        store.createLayer("light");
        break;
      case "createControl":
        store.createLayer("control");
        break;
      case "createParticle":
        store.createLayer("particle");
        break;
      case "createDepth":
        store.createLayer("depth");
        break;
      case "createNormal":
        store.createLayer("normal");
        break;
      case "createGenerated":
        store.createLayer("generated");
        break;
      case "createGroup":
        store.createLayer("group");
        break;
      case "createEffectLayer":
        store.createLayer("effectLayer");
        break;
      case "createMatte":
        store.createLayer("matte");
        break;

      // Layer menu
      case "precompose":
        showPrecomposeDialog.value = true;
        break;
      case "splitLayer":
        store.splitLayerAtPlayhead();
        break;
      case "timeStretch":
        showTimeStretchDialog.value = true;
        break;
      case "timeReverse":
        store.reverseSelectedLayers();
        break;
      case "freezeFrame":
        store.freezeFrameAtPlayhead();
        break;
      case "lockLayer":
        store.toggleLayerLock();
        break;
      case "toggleVisibility":
        store.toggleLayerVisibility();
        break;
      case "isolateLayer":
        store.toggleLayerSolo();
        break;
      case "bringToFront":
        store.bringToFront();
        break;
      case "sendToBack":
        store.sendToBack();
        break;
      case "bringForward":
        store.bringForward();
        break;
      case "sendBackward":
        store.sendBackward();
        break;

      // View menu
      case "zoomIn":
        handleZoomIn();
        break;
      case "zoomOut":
        handleZoomOut();
        break;
      case "zoomFit":
        viewZoom.value = "fit";
        handleZoomChange();
        break;
      case "zoom100":
        viewZoom.value = "100";
        handleZoomChange();
        break;
      case "toggleCurveEditor":
        showCurveEditor.value = !showCurveEditor.value;
        break;

      // Window menu - panel visibility
      case "showProperties":
        expandedPanels.value.properties = true;
        break;
      case "showEffects":
        leftTab.value = "effects";
        break;
      case "showCamera":
        expandedPanels.value.camera = true;
        break;
      case "showAudio":
        expandedPanels.value.audio = true;
        break;
      case "showAlign":
        expandedPanels.value.align = true;
        break;
      case "showAIChat":
        aiTab.value = "chat";
        break;
      case "showAIGenerate":
        aiTab.value = "generate";
        break;
      case "showExport":
        showExportDialog.value = true;
        break;
      case "showPreview":
        showHDPreview.value = true;
        break;

      // Help menu
      case "showKeyboardShortcuts":
        showPreferencesDialog.value = true;
        break;
      case "showDocumentation":
        window.open(
          "https://github.com/justinfleek/lattice-compositor",
          "_blank",
        );
        break;
      case "showAbout":
        alert(
          "Lattice Compositor v7.6\n\nProfessional motion graphics compositor for ComfyUI.\n\nBuilt with Vue 3, Three.js, and Pinia.",
        );
        break;

      default:
        console.warn("Unhandled menu action:", action);
    }
  }

  return {
    handleMenuAction,
    handleZoomIn,
    handleZoomOut,
  };
}
