/**
 * Text to Spline Conversion
 *
 * Converts text layers to vector spline layers using font vectorization.
 */

import { textToVectorFromUrl } from "@/services/textToVector";
import type { BezierPath } from "@/types/shapes";
import type { ControlPoint, SplineData } from "@/types/project";
import { createAnimatableProperty, createDefaultTransform } from "@/types/project";
import { storeLogger } from "@/utils/logger";
import { useSelectionStore } from "../selectionStore";
import type { CompositorStoreAccess } from "./types";

// ============================================================================
// TEXT TO SPLINE CONVERSION
// ============================================================================

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
 * @param compositorStore - The compositor store instance
 * @param layerId - ID of the text layer to convert
 * @param options - Conversion options
 * @returns Array of created spline layer IDs, or null on failure
 */
export async function convertTextLayerToSplines(
  compositorStore: CompositorStoreAccess,
  layerId: string,
  options: ConvertTextToSplinesOptions = {},
): Promise<string[] | null> {
  const layers = compositorStore.getActiveCompLayers();
  const layer = layers.find((l) => l.id === layerId);

  if (!layer || layer.type !== "text") {
    storeLogger.error(
      "convertTextLayerToSplines: Layer not found or not a text layer",
    );
    return null;
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
    storeLogger.error("convertTextLayerToSplines: No text content");
    return null;
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
      storeLogger.error("convertTextLayerToSplines: No paths generated");
      return null;
    }

    compositorStore.pushHistory();

    const createdLayerIds: string[] = [];

    if (options.perCharacter && result.characters.length > 0) {
      // Create parent group layer if requested
      let parentId: string | null = layer.parentId ?? null;

      if (options.groupCharacters) {
        // Use compositorStore.createLayer which delegates to layerStore
        const groupLayer = compositorStore.createLayer!("null", `${layer.name} (Group)`);
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
        const charLayer = compositorStore.createLayer!("spline", charLayerName);

        // Set up spline data
        const splineData: SplineData = {
          pathData: "",
          controlPoints: allControlPoints,
          closed: charGroup.paths[0]?.closed ?? true,
          stroke: textData.stroke || "",
          strokeWidth: textData.strokeWidth || 0,
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
        storeLogger.error(
          "convertTextLayerToSplines: No control points generated",
        );
        return null;
      }

      const splineLayer = compositorStore.createLayer!(
        "spline",
        `${layer.name} (Spline)`,
      );

      const splineData: SplineData = {
        pathData: "",
        controlPoints: allControlPoints,
        closed: result.allPaths[0]?.closed ?? true,
        stroke: textData.stroke || "",
        strokeWidth: textData.strokeWidth || 0,
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
      compositorStore.deleteLayer!(layerId);
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
    storeLogger.error("convertTextLayerToSplines: Failed to convert", error);
    return null;
  }
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

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
