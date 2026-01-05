import { ref } from "vue";

export interface Guide {
  id: string;
  orientation: "horizontal" | "vertical";
  position: number;
}

export interface GuideContextMenu {
  visible: boolean;
  x: number;
  y: number;
  guideId: string | null;
}

export function useGuides() {
  const guides = ref<Guide[]>([]);
  const draggingGuide = ref<{
    id: string;
    orientation: "horizontal" | "vertical";
  } | null>(null);

  const guideContextMenu = ref<GuideContextMenu>({
    visible: false,
    x: 0,
    y: 0,
    guideId: null,
  });

  function addGuide(orientation: "horizontal" | "vertical", position: number) {
    const id = `guide-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;
    guides.value.push({ id, orientation, position });
    console.log(`[Lattice] Added ${orientation} guide at ${position}px`);
  }

  function removeGuide(id: string) {
    guides.value = guides.value.filter((g) => g.id !== id);
  }

  function clearGuides() {
    guides.value = [];
    console.log("[Lattice] Cleared all guides");
  }

  function updateGuidePosition(id: string, position: number) {
    const guide = guides.value.find((g) => g.id === id);
    if (guide) {
      guide.position = position;
    }
  }

  function showGuideContextMenu(guide: Guide, event: MouseEvent) {
    guideContextMenu.value = {
      visible: true,
      x: event.clientX,
      y: event.clientY,
      guideId: guide.id,
    };
    setTimeout(() => {
      document.addEventListener("click", hideGuideContextMenu, { once: true });
    }, 0);
  }

  function hideGuideContextMenu() {
    guideContextMenu.value.visible = false;
    guideContextMenu.value.guideId = null;
  }

  function deleteGuideFromMenu() {
    if (guideContextMenu.value.guideId) {
      removeGuide(guideContextMenu.value.guideId);
    }
    hideGuideContextMenu();
  }

  function clearAllGuides() {
    clearGuides();
    hideGuideContextMenu();
  }

  function getGuideStyle(guide: Guide) {
    if (guide.orientation === "horizontal") {
      return {
        position: "absolute" as const,
        left: 0,
        right: 0,
        top: `${guide.position - 5}px`,
        height: "11px",
        background:
          "linear-gradient(to bottom, transparent 5px, #00BFFF 5px, #00BFFF 6px, transparent 6px)",
        cursor: "ns-resize",
        zIndex: 10,
      };
    } else {
      return {
        position: "absolute" as const,
        top: 0,
        bottom: 0,
        left: `${guide.position - 5}px`,
        width: "11px",
        background:
          "linear-gradient(to right, transparent 5px, #00BFFF 5px, #00BFFF 6px, transparent 6px)",
        cursor: "ew-resize",
        zIndex: 10,
      };
    }
  }

  function createGuideFromRuler(
    orientation: "horizontal" | "vertical",
    event: MouseEvent,
  ) {
    const rect = (event.currentTarget as HTMLElement).getBoundingClientRect();
    let position: number;

    if (orientation === "horizontal") {
      position = event.clientY - rect.top;
    } else {
      position = event.clientX - rect.left;
    }

    addGuide(orientation, position);
  }

  function startGuideDrag(guide: Guide, event: MouseEvent) {
    event.preventDefault();
    draggingGuide.value = { id: guide.id, orientation: guide.orientation };

    const handleMove = (e: MouseEvent) => {
      if (!draggingGuide.value) return;

      const viewportContent = document.querySelector(".viewport-content");
      if (!viewportContent) return;

      const rect = viewportContent.getBoundingClientRect();
      let newPosition: number;

      if (draggingGuide.value.orientation === "horizontal") {
        newPosition = e.clientY - rect.top;
      } else {
        newPosition = e.clientX - rect.left;
      }

      // Remove guide if dragged off the viewport
      if (
        newPosition < 0 ||
        newPosition >
          (draggingGuide.value.orientation === "horizontal"
            ? rect.height
            : rect.width)
      ) {
        removeGuide(draggingGuide.value.id);
        draggingGuide.value = null;
        window.removeEventListener("mousemove", handleMove);
        window.removeEventListener("mouseup", handleUp);
        return;
      }

      updateGuidePosition(draggingGuide.value.id, newPosition);
    };

    const handleUp = () => {
      draggingGuide.value = null;
      window.removeEventListener("mousemove", handleMove);
      window.removeEventListener("mouseup", handleUp);
    };

    window.addEventListener("mousemove", handleMove);
    window.addEventListener("mouseup", handleUp);
  }

  return {
    guides,
    guideContextMenu,
    draggingGuide,
    addGuide,
    removeGuide,
    clearGuides,
    updateGuidePosition,
    showGuideContextMenu,
    hideGuideContextMenu,
    deleteGuideFromMenu,
    clearAllGuides,
    getGuideStyle,
    createGuideFromRuler,
    startGuideDrag,
  };
}
