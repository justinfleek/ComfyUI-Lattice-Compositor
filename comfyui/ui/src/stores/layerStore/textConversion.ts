/**
 * Text to Spline Conversion
 *
 * Converts text layers to vector spline layers using font vectorization.
 */

import { isFiniteNumber, safeNonNegativeDefault } from "@/utils/typeGuards";
import { textToVectorFromUrl } from "@/services/textToVector";
import type { BezierPath } from "@/types/shapes";
import type { ControlPoint, SplineData } from "@/types/project";
import { createAnimatableProperty, createDefaultTransform } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "../selectionStore";
import { useProjectStore } from "../projectStore";
import { createLayer, deleteLayer } from "./crud";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // text // to // spline // conversion
// ═══════════════════════════════════════════════════════════════════════════

export interface ConvertTextToSplinesOptions {
  /** Create separate layer per character */
  perCharacter?: boolean;
  /** Font URL to use (required if font not loaded) */
  fontUrl?: string;
  /** Keep original text layer */
  keepOriginal?: boolean;
  /** Group character layers under a null parent */
  groupCharacters?: boolean;
}

/**
 * Convert a text layer to one or more spline layers
 *
 * @param layerId - ID of the text layer to convert
 * @param options - Conversion options
 * @returns Array of created spline layer IDs, or null on failure
 */
export async function convertTextLayerToSplines(
  layerId: string,
  options: ConvertTextToSplinesOptions = {},
): Promise<string[] | null> {
  const projectStore = useProjectStore();
  const layers = projectStore.getActiveCompLayers();
  const layer = layers.find((l) => l.id === layerId);

  if (!layer || layer.type !== "text") {
    throw new Error(`[LayerStore] Cannot convert text layer to splines: Layer "${layerId}" not found or is not a text layer`);
  }

  const textData = layer.data as {
    text: string;
    fontFamily: string;
    fontSize: number;
    fill: string;
    stroke: string;
    strokeWidth: number;
  };

  if (!textData.text) {
    throw new Error(`[LayerStore] Cannot convert text layer to splines: Layer "${layerId}" has no text content`);
  }

  // Get font URL - use Google Fonts CDN as fallback
  const fontUrl =
    options.fontUrl ||
    `https://fonts.gstatic.com/s/${textData.fontFamily.toLowerCase().replace(/\s+/g, "")}/v1/regular.woff`;

  try {
    // Convert text to vector paths
    const result = await textToVectorFromUrl(
      textData.text,
      fontUrl,
      textData.fontSize,
      {
        x: layer.transform.position.value.x,
        y: layer.transform.position.value.y,
        kerning: true,
      },
    );

    if (!result.allPaths.length && !result.characters.length) {
      throw new Error(`[LayerStore] Cannot convert text layer to splines: No paths generated for layer "${layerId}"`);
    }

    projectStore.pushHistory();

    const createdLayerIds: string[] = [];

    if (options.perCharacter && result.characters.length > 0) {
      // Create parent group layer if requested
      // Type proof: parentId ∈ string | null | undefined → string | null
      const parentIdValue = layer.parentId;
      let parentId: string | null = typeof parentIdValue === "string" ? parentIdValue : null;

      if (options.groupCharacters) {
        // Use createLayer directly from crud module
        const groupLayer = createLayer("null", `${layer.name} (Group)`);
        groupLayer.transform = { ...layer.transform };
        parentId = groupLayer.id;
        createdLayerIds.push(groupLayer.id);
      }

      // Create one spline layer per character
      for (let i = 0; i < result.characters.length; i++) {
        const charGroup = result.characters[i];

        // Skip whitespace characters
        if (charGroup.character.trim() === "" || charGroup.paths.length === 0) {
          continue;
        }

        // Combine all paths for this character into one
        const allControlPoints: ControlPoint[] = [];
        for (const path of charGroup.paths) {
          const points = bezierPathToControlPoints(path);
          allControlPoints.push(...points);
        }

        if (allControlPoints.length === 0) continue;

        const charLayerName = `${layer.name} - "${charGroup.character}" [${i}]`;
        const charLayer = createLayer("spline", charLayerName);

        // Set up spline data
        const splineData: SplineData = {
          pathData: "",
          controlPoints: allControlPoints,
          // Type proof: closed ∈ boolean | undefined → boolean
          closed: (() => {
            // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
            const firstPath = (charGroup.paths != null && Array.isArray(charGroup.paths) && charGroup.paths.length > 0) ? charGroup.paths[0] : undefined;
            const closedValue = (firstPath != null && typeof firstPath === "object" && "closed" in firstPath && typeof firstPath.closed === "boolean" && firstPath.closed) ? true : undefined;
            return closedValue === true;
          })(),
          stroke: textData.stroke || "",
          // Type proof: strokeWidth ∈ number | undefined → number (≥ 0, stroke width)
          strokeWidth: safeNonNegativeDefault(textData.strokeWidth, 0, "textData.strokeWidth"),
          fill: textData.fill || "#ffffff",
        };

        charLayer.data = splineData;
        charLayer.parentId = parentId;
        charLayer.inPoint = layer.inPoint;
        charLayer.outPoint = layer.outPoint;

        // Position relative to character bounds
        if (!options.groupCharacters) {
          charLayer.transform = {
            ...createDefaultTransform(),
            position: createAnimatableProperty(
              "Position",
              {
                x: layer.transform.position.value.x + charGroup.bounds.x,
                y: layer.transform.position.value.y,
              },
              "position",
            ),
          };
        }

        createdLayerIds.push(charLayer.id);
      }
    } else {
      // Create single spline layer with all paths
      const allControlPoints: ControlPoint[] = [];

      for (const path of result.allPaths) {
        const points = bezierPathToControlPoints(path);
        allControlPoints.push(...points);
      }

      if (allControlPoints.length === 0) {
        throw new Error(`[LayerStore] Cannot convert text layer to splines: No control points generated for layer "${layerId}"`);
      }

      const splineLayer = createLayer(
        "spline",
        `${layer.name} (Spline)`,
      );

      const splineData: SplineData = {
        pathData: "",
        controlPoints: allControlPoints,
        // Type proof: closed ∈ boolean | undefined → boolean
        closed: (() => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
          const firstPath = (result.allPaths != null && Array.isArray(result.allPaths) && result.allPaths.length > 0) ? result.allPaths[0] : undefined;
          const closedValue = (firstPath != null && typeof firstPath === "object" && "closed" in firstPath && typeof firstPath.closed === "boolean" && firstPath.closed) ? true : undefined;
          return closedValue === true;
        })(),
        stroke: textData.stroke || "",
        // Type proof: strokeWidth ∈ number | undefined → number (≥ 0, stroke width)
        strokeWidth: safeNonNegativeDefault(textData.strokeWidth, 0, "textData.strokeWidth"),
        fill: textData.fill || "#ffffff",
      };

      splineLayer.data = splineData;
      splineLayer.transform = { ...layer.transform };
      splineLayer.parentId = layer.parentId;
      splineLayer.inPoint = layer.inPoint;
      splineLayer.outPoint = layer.outPoint;

      createdLayerIds.push(splineLayer.id);
    }

    // Remove original layer if not keeping
    if (!options.keepOriginal) {
      deleteLayer(layerId);
    }

    // Select the first created layer
    if (createdLayerIds.length > 0) {
      const selectionStore = useSelectionStore();
      selectionStore.clearLayerSelection();
      selectionStore.selectLayer(createdLayerIds[0]);
    }

    storeLogger.info(
      `Converted text layer to ${createdLayerIds.length} spline layer(s)`,
    );
    return createdLayerIds;
  } catch (error) {
    if (error instanceof Error && error.message.startsWith("[LayerStore]")) {
      throw error;
    }
    throw new Error(`[LayerStore] Failed to convert text layer to splines: ${error instanceof Error ? error.message : String(error)}`);
  }
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                      // helper // functions
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Convert BezierPath vertices to ControlPoint format
 */
function bezierPathToControlPoints(path: BezierPath): ControlPoint[] {
  return path.vertices.map((vertex, index) => {
    // BezierVertex handles are RELATIVE, ControlPoint handles are ABSOLUTE
    const handleIn =
      vertex.inHandle.x !== 0 || vertex.inHandle.y !== 0
        ? {
            x: vertex.point.x + vertex.inHandle.x,
            y: vertex.point.y + vertex.inHandle.y,
          }
        : null;

    const handleOut =
      vertex.outHandle.x !== 0 || vertex.outHandle.y !== 0
        ? {
            x: vertex.point.x + vertex.outHandle.x,
            y: vertex.point.y + vertex.outHandle.y,
          }
        : null;

    return {
      id: `cp_${Date.now()}_${index}_${Math.random().toString(36).slice(2, 6)}`,
      x: vertex.point.x,
      y: vertex.point.y,
      depth: 0,
      handleIn,
      handleOut,
      type: handleIn || handleOut ? ("smooth" as const) : ("corner" as const),
    };
  });
}
