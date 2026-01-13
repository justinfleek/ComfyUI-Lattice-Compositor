/**
 * Menu Actions Composable
 *
 * Handles all menu bar action dispatching for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import { useCompositorStore } from "@/stores/compositorStore";
import { useLayerStore } from "@/stores/layerStore";
import { useHistoryStore } from "@/stores/historyStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useMarkerStore } from "@/stores/markerStore";
import { useProjectStore } from "@/stores/projectStore";

export interface MenuActionsOptions {
  // Dialog refs
  showExportDialog: Ref<boolean>;
  showPrecomposeDialog: Ref<boolean>;
  showTimeStretchDialog: Ref<boolean>;
  showFrameInterpolationDialog: Ref<boolean>;
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
  const store = useCompositorStore();
  const layerStore = useLayerStore();
  const _historyStore = useHistoryStore();
  const animationStore = useAnimationStore();
  const markerStore = useMarkerStore();
  const projectStore = useProjectStore();

  const {
    showExportDialog,
    showPrecomposeDialog,
    showTimeStretchDialog,
    showFrameInterpolationDialog,
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
          projectStore.newProject(store);
        }
        break;
      case "openProject":
        triggerProjectOpen();
        break;
      case "saveProject":
        projectStore.saveProject(store);
        break;
      case "saveProjectAs":
        projectStore.saveProjectAs(store).then((projectId: string | null) => {
          if (projectId) {
            alert(`Project saved with ID: ${projectId}`);
          } else {
            alert("Failed to save project");
          }
        });
        break;
      case "import":
        triggerAssetImport();
        break;
      case "export":
        showExportDialog.value = true;
        break;

      // Server operations
      case "saveProjectToServer":
        store.saveProjectToServer().then((projectId: string | null) => {
          if (projectId) {
            alert(`Project saved to server with ID: ${projectId}`);
          } else {
            alert("Failed to save project to server");
          }
        });
        break;
      case "loadProjectFromServer":
        // For now, prompt for project ID - later can add a project browser dialog
        {
          const projectId = prompt("Enter project ID to load:");
          if (projectId) {
            store.loadProjectFromServer(projectId).then((success: boolean) => {
              if (success) {
                alert("Project loaded from server");
              } else {
                alert("Failed to load project from server");
              }
            });
          }
        }
        break;

      // Edit menu
      case "undo":
        store.undo();
        break;
      case "redo":
        store.redo();
        break;
      case "cut":
        layerStore.cutSelectedLayers(store);
        break;
      case "copy":
        layerStore.copySelectedLayers(store);
        break;
      case "paste":
        layerStore.pasteLayers(store);
        break;
      case "duplicate":
        layerStore.duplicateSelectedLayers(store);
        break;
      case "delete":
        layerStore.deleteSelectedLayers(store);
        break;
      case "selectAll":
        layerStore.selectAllLayers(store);
        break;
      case "deselectAll":
        layerStore.clearSelection(store);
        break;

      // Markers
      case "addMarkerAtPlayhead":
        markerStore.addMarkers(store, [
          {
            frame: animationStore.getCurrentFrame(store),
            label: `Marker ${markerStore.getMarkers(store).length + 1}`,
            color: "#FFFF00",
          },
        ]);
        break;
      case "jumpToNextMarker":
        markerStore.jumpToNextMarker(store);
        break;
      case "jumpToPreviousMarker":
        markerStore.jumpToPreviousMarker(store);
        break;
      case "clearMarkers":
        if (confirm("Clear all markers?")) {
          markerStore.clearMarkers(store);
        }
        break;

      // Cache operations
      case "clearFrameCache":
        store.clearFrameCache();
        break;

      // Create menu - layer types
      case "createSolid":
        layerStore.createLayer(store, "solid");
        break;
      case "createText":
        layerStore.createTextLayer(store);
        break;
      case "createShape":
        layerStore.createSplineLayer(store);
        break;
      case "createPath":
        layerStore.createLayer(store, "path");
        break;
      case "createCamera":
        layerStore.createCameraLayer(store);
        break;
      case "createLight":
        layerStore.createLayer(store, "light");
        break;
      case "createControl":
        layerStore.createLayer(store, "control");
        break;
      case "createParticle":
        layerStore.createLayer(store, "particle");
        break;
      case "createDepth":
        layerStore.createLayer(store, "depth");
        break;
      case "createNormal":
        layerStore.createLayer(store, "normal");
        break;
      case "createGenerated":
        layerStore.createLayer(store, "generated");
        break;
      case "createGroup":
        layerStore.createLayer(store, "group");
        break;
      case "createEffectLayer":
        layerStore.createLayer(store, "effectLayer");
        break;
      case "createMatte":
        layerStore.createLayer(store, "matte");
        break;

      // Layer menu
      case "precompose":
        showPrecomposeDialog.value = true;
        break;
      case "splitLayer":
        {
          const selectedIds = store.selectedLayerIds;
          if (selectedIds.length > 0) {
            layerStore.splitLayerAtPlayhead(store, selectedIds[0]);
          }
        }
        break;
      case "timeStretch":
        showTimeStretchDialog.value = true;
        break;
      case "frameInterpolation":
        showFrameInterpolationDialog.value = true;
        break;
      case "timeReverse":
        {
          const selectedIds = store.selectedLayerIds;
          for (const id of selectedIds) {
            layerStore.reverseLayer(store, id);
          }
        }
        break;
      case "freezeFrame":
        {
          const selectedIds = store.selectedLayerIds;
          if (selectedIds.length > 0) {
            layerStore.freezeFrameAtPlayhead(store, selectedIds[0]);
          }
        }
        break;
      case "lockLayer":
        layerStore.toggleLayerLock(store);
        break;
      case "toggleVisibility":
        layerStore.toggleLayerVisibility(store);
        break;
      case "isolateLayer":
        layerStore.toggleLayerSolo(store);
        break;
      case "bringToFront":
        layerStore.bringToFront(store);
        break;
      case "sendToBack":
        layerStore.sendToBack(store);
        break;
      case "bringForward":
        layerStore.bringForward(store);
        break;
      case "sendBackward":
        layerStore.sendBackward(store);
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
