/**
 * Menu Actions Composable
 *
 * Handles all menu bar action dispatching for the WorkspaceLayout.
 * Extracted from WorkspaceLayout.vue to reduce file size and improve maintainability.
 */

import type { Ref } from "vue";
import { useLayerStore } from "@/stores/layerStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useMarkerStore } from "@/stores/markerStore";
import { useProjectStore } from "@/stores/projectStore";
import { useSelectionStore } from "@/stores/selectionStore";
import { useCacheStore } from "@/stores/cacheStore";
import { useCameraStore } from "@/stores/cameraStore";
import type { MarkerStoreAccess } from "@/stores/markerStore";
import type { AnimationStoreAccess } from "@/stores/animationStore/types";
import { usePlaybackStore } from "@/stores/playbackStore";
import { isFiniteNumber } from "@/utils/typeGuards";

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
  const layerStore = useLayerStore();
  const animationStore = useAnimationStore();
  const markerStore = useMarkerStore();
  const projectStore = useProjectStore();
  const selectionStore = useSelectionStore();
  const cacheStore = useCacheStore();
  const cameraStore = useCameraStore();
  const playbackStore = usePlaybackStore();

  // Helper to create MarkerStoreAccess for marker operations
  function getMarkerStoreAccess(): MarkerStoreAccess {
    const activeComp = projectStore.getActiveComp();
    return {
      project: {
        compositions: projectStore.project.compositions,
        meta: projectStore.project.meta,
      },
      activeCompositionId: projectStore.activeCompositionId,
      // Lean4/PureScript/Haskell: Explicit pattern matching on optional property
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
      currentFrame: (() => {
        if (activeComp !== null && typeof activeComp === "object" && "currentFrame" in activeComp && typeof activeComp.currentFrame === "number") {
          return activeComp.currentFrame;
        }
        return 0;
      })(),
      getActiveComp: () => projectStore.getActiveComp(),
      setFrame: (frame: number) => {
        const comp = projectStore.getActiveComp();
        if (comp) {
          comp.currentFrame = frame;
        }
      },
      pushHistory: () => projectStore.pushHistory(),
    };
  }

  // Helper to create AnimationStoreAccess for animation operations
  function getAnimationStoreAccess(): AnimationStoreAccess {
    const activeComp = projectStore.getActiveComp();
    return {
      isPlaying: playbackStore.isPlaying,
      getActiveComp: () => projectStore.getActiveComp(),
      get currentFrame() {
        const comp = projectStore.getActiveComp();
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        if (comp !== null && typeof comp === "object" && "currentFrame" in comp && typeof comp.currentFrame === "number") {
          return comp.currentFrame;
        }
        return 0;
      },
      get frameCount() {
        const comp = projectStore.getActiveComp();
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy optional chaining
        if (comp !== null && typeof comp === "object" && "settings" in comp && comp.settings !== null && typeof comp.settings === "object" && "frameCount" in comp.settings && typeof comp.settings.frameCount === "number") {
          return comp.settings.frameCount;
        }
        return 81;
      },
      get fps() {
        return projectStore.getFps();
      },
      getActiveCompLayers: () => projectStore.getActiveCompLayers(),
      getLayerById: (id: string) => {
        const layers = projectStore.getActiveCompLayers();
        return layers.find(l => l.id === id) || null;
      },
      project: {
        composition: {
          width: projectStore.project.composition.width,
          height: projectStore.project.composition.height,
        },
        meta: projectStore.project.meta,
      },
      pushHistory: () => projectStore.pushHistory(),
    };
  }

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
          projectStore.newProject();
        }
        break;
      case "openProject":
        triggerProjectOpen();
        break;
      case "saveProject":
        projectStore.saveProject();
        break;
      case "saveProjectAs":
        projectStore.saveProjectAs().then((projectId: string | null) => {
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
        projectStore.saveProjectToServer().then((projectId: string | null) => {
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
            projectStore.loadProjectFromServer(projectId, () => projectStore.pushHistory()).then((success: boolean) => {
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
        projectStore.undo();
        break;
      case "redo":
        projectStore.redo();
        break;
      case "cut":
        layerStore.cutSelectedLayers();
        break;
      case "copy":
        layerStore.copySelectedLayers();
        break;
      case "paste":
        layerStore.pasteLayers();
        break;
      case "duplicate":
        layerStore.duplicateSelectedLayers();
        break;
      case "delete":
        layerStore.deleteSelectedLayers();
        break;
      case "selectAll":
        layerStore.selectAllLayers();
        break;
      case "deselectAll":
        layerStore.clearSelection();
        break;

      // Markers
      case "addMarkerAtPlayhead": {
        const markerAccess = getMarkerStoreAccess();
        markerStore.addMarkers(markerAccess, [
          {
            frame: markerAccess.currentFrame,
            label: `Marker ${markerStore.getMarkers(markerAccess).length + 1}`,
            color: "#FFFF00",
          },
        ]);
        break;
      }
      case "jumpToNextMarker":
        markerStore.jumpToNextMarker(getMarkerStoreAccess());
        break;
      case "jumpToPreviousMarker":
        markerStore.jumpToPreviousMarker(getMarkerStoreAccess());
        break;
      case "clearMarkers":
        if (confirm("Clear all markers?")) {
          markerStore.clearMarkers(getMarkerStoreAccess());
        }
        break;

      // Cache operations
      case "clearFrameCache":
        cacheStore.clearFrameCache();
        break;

      // Create menu - layer types
      case "createSolid":
        layerStore.createLayer("solid");
        break;
      case "createText": {
        layerStore.createTextLayer();
        break;
      }
      case "createShape": {
        layerStore.createSplineLayer();
        break;
      }
      case "createPath":
        layerStore.createLayer("path");
        break;
      case "createCamera": {
        layerStore.createCameraLayer();
        break;
      }
      case "createLight":
        layerStore.createLayer("light");
        break;
      case "createControl":
        layerStore.createLayer("control");
        break;
      case "createParticle":
        layerStore.createLayer("particle");
        break;
      case "createDepth":
        layerStore.createLayer("depth");
        break;
      case "createNormal":
        layerStore.createLayer("normal");
        break;
      case "createGenerated":
        layerStore.createLayer("generated");
        break;
      case "createGroup":
        layerStore.createLayer("group");
        break;
      case "createEffectLayer":
        layerStore.createLayer("effectLayer");
        break;
      case "createMatte":
        layerStore.createLayer("matte");
        break;

      // Layer menu
      case "precompose":
        showPrecomposeDialog.value = true;
        break;
      case "splitLayer":
        {
          const selectedIds = selectionStore.selectedLayerIds;
          if (selectedIds.length > 0) {
            layerStore.splitLayerAtPlayhead(selectedIds[0]);
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
          const selectedIds = selectionStore.selectedLayerIds;
          for (const id of selectedIds) {
            layerStore.reverseLayer(id);
          }
        }
        break;
      case "freezeFrame":
        {
          const selectedIds = selectionStore.selectedLayerIds;
          if (selectedIds.length > 0) {
            layerStore.freezeFrameAtPlayhead(selectedIds[0]);
          }
        }
        break;
      case "lockLayer":
        layerStore.toggleLayerLock();
        break;
      case "toggleVisibility":
        layerStore.toggleLayerVisibility();
        break;
      case "isolateLayer":
        layerStore.toggleLayerSolo();
        break;
      case "bringToFront":
        layerStore.bringToFront();
        break;
      case "sendToBack":
        layerStore.sendToBack();
        break;
      case "bringForward":
        layerStore.bringForward();
        break;
      case "sendBackward":
        layerStore.sendBackward();
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
