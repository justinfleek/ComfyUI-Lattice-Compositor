/**
 * SVG Export Service
 *
 * Exports spline layers and compositions to SVG format.
 */

import type { ControlPoint, Layer, SplineData } from "@/types/project";
import { createLogger } from "@/utils/logger";

const _logger = createLogger("SVGExport");

export interface SVGExportOptions {
  includeStrokes?: boolean;
  includeFills?: boolean;
  precision?: number;
  viewBox?: { x: number; y: number; width: number; height: number };
  includeTransforms?: boolean;
  includeMetadata?: boolean;
  minify?: boolean;
}

export interface SVGExportResult {
  svg: string;
  width: number;
  height: number;
  pathCount: number;
  warnings: string[];
}

const DEFAULT_OPTIONS: Required<SVGExportOptions> = {
  includeStrokes: true,
  includeFills: true,
  precision: 3,
  viewBox: { x: 0, y: 0, width: 1920, height: 1080 },
  includeTransforms: true,
  includeMetadata: true,
  minify: false,
};

export class SVGExportService {
  private options: Required<SVGExportOptions>;

  constructor(options?: SVGExportOptions) {
    this.options = { ...DEFAULT_OPTIONS, ...options };
  }

  exportSplineLayer(layer: Layer, options?: SVGExportOptions): SVGExportResult {
    const opts = { ...this.options, ...options };
    const warnings: string[] = [];

    if (layer.type !== "spline" || !layer.data) {
      warnings.push("Layer is not a spline layer");
      return { svg: "", width: 0, height: 0, pathCount: 0, warnings };
    }

    const splineData = layer.data as SplineData;
    const pathData = this.controlPointsToPathData(
      splineData.controlPoints,
      splineData.closed ?? false,
      opts.precision,
    );

    const strokeAttr = opts.includeStrokes
      ? 'stroke="' +
        (splineData.stroke || "#000") +
        '" stroke-width="' +
        (splineData.strokeWidth || 1) +
        '"'
      : 'stroke="none"';

    const fillAttr = opts.includeFills
      ? `fill="${splineData.fill || "none"}"`
      : 'fill="none"';

    let transformAttr = "";
    if (opts.includeTransforms && layer.transform) {
      transformAttr = this.buildTransformAttribute(layer);
    }

    const bounds = this.calculateBounds(splineData.controlPoints);
    const viewBox = opts.viewBox || {
      x: bounds.minX - 10,
      y: bounds.minY - 10,
      width: bounds.maxX - bounds.minX + 20,
      height: bounds.maxY - bounds.minY + 20,
    };

    const nl = opts.minify ? "" : "\n";
    const ind = opts.minify ? "" : "  ";

    let svg = `<?xml version="1.0" encoding="UTF-8"?>${nl}`;
    svg += '<svg xmlns="http://www.w3.org/2000/svg" ';
    svg +=
      'viewBox="' +
      viewBox.x +
      " " +
      viewBox.y +
      " " +
      viewBox.width +
      " " +
      viewBox.height +
      '" ';
    svg += `width="${viewBox.width}" height="${viewBox.height}">${nl}`;

    if (opts.includeMetadata) {
      svg += `${ind}<!-- Exported from Lattice Compositor -->${nl}`;
    }

    const trAttr = transformAttr ? ` transform="${transformAttr}"` : "";
    svg +=
      ind +
      '<path d="' +
      pathData +
      '" ' +
      strokeAttr +
      " " +
      fillAttr +
      trAttr +
      "/>" +
      nl;
    svg += "</svg>";

    return {
      svg,
      width: viewBox.width,
      height: viewBox.height,
      pathCount: 1,
      warnings,
    };
  }

  exportComposition(
    composition: { settings: { width: number; height: number } },
    layers: Layer[],
    options?: SVGExportOptions,
  ): SVGExportResult {
    const opts = { ...this.options, ...options };
    const warnings: string[] = [];
    const width = composition.settings.width;
    const height = composition.settings.height;
    const viewBox = opts.viewBox || { x: 0, y: 0, width, height };

    const nl = opts.minify ? "" : "\n";
    const ind = opts.minify ? "" : "  ";

    let svg = `<?xml version="1.0" encoding="UTF-8"?>${nl}`;
    svg += '<svg xmlns="http://www.w3.org/2000/svg" ';
    svg +=
      'viewBox="' +
      viewBox.x +
      " " +
      viewBox.y +
      " " +
      viewBox.width +
      " " +
      viewBox.height +
      '" ';
    svg += `width="${width}" height="${height}">${nl}`;

    let pathCount = 0;

    for (const layer of layers) {
      if (layer.type !== "spline" || !layer.data) continue;

      const splineData = layer.data as SplineData;
      const pathData = this.controlPointsToPathData(
        splineData.controlPoints,
        splineData.closed ?? false,
        opts.precision,
      );

      const strokeAttr = opts.includeStrokes
        ? 'stroke="' +
          (splineData.stroke || "#000") +
          '" stroke-width="' +
          (splineData.strokeWidth || 1) +
          '"'
        : 'stroke="none"';

      const fillAttr = opts.includeFills
        ? `fill="${splineData.fill || "none"}"`
        : 'fill="none"';

      let transformAttr = "";
      if (opts.includeTransforms && layer.transform) {
        transformAttr = this.buildTransformAttribute(layer);
      }

      const trAttr = transformAttr ? ` transform="${transformAttr}"` : "";
      svg += `${ind}<g id="${this.sanitizeId(layer.id)}">${nl}`;
      svg +=
        ind +
        ind +
        '<path d="' +
        pathData +
        '" ' +
        strokeAttr +
        " " +
        fillAttr +
        trAttr +
        "/>" +
        nl;
      svg += `${ind}</g>${nl}`;
      pathCount++;
    }

    svg += "</svg>";
    return { svg, width, height, pathCount, warnings };
  }

  controlPointsToPathData(
    points: ControlPoint[],
    closed: boolean,
    precision: number = 3,
  ): string {
    if (points.length === 0) return "";

    const fmt = (n: number) => n.toFixed(precision).replace(/.?0+$/, "");

    let d = `M${fmt(points[0].x)},${fmt(points[0].y)}`;

    for (let i = 0; i < points.length - 1; i++) {
      const curr = points[i];
      const next = points[i + 1];
      const cp1 = curr.handleOut || { x: curr.x, y: curr.y };
      const cp2 = next.handleIn || { x: next.x, y: next.y };

      const isLine =
        Math.abs(cp1.x - curr.x) < 0.01 &&
        Math.abs(cp1.y - curr.y) < 0.01 &&
        Math.abs(cp2.x - next.x) < 0.01 &&
        Math.abs(cp2.y - next.y) < 0.01;

      if (isLine) {
        d += ` L${fmt(next.x)},${fmt(next.y)}`;
      } else {
        d +=
          " C" +
          fmt(cp1.x) +
          "," +
          fmt(cp1.y) +
          " " +
          fmt(cp2.x) +
          "," +
          fmt(cp2.y) +
          " " +
          fmt(next.x) +
          "," +
          fmt(next.y);
      }
    }

    if (closed && points.length > 1) {
      d += " Z";
    }

    return d;
  }

  private buildTransformAttribute(layer: Layer): string {
    const transforms: string[] = [];
    const t = layer.transform;
    if (!t) return "";

    const pos = t.position?.value as { x?: number; y?: number } | undefined;
    if (pos && (pos.x || pos.y)) {
      transforms.push(`translate(${pos.x || 0},${pos.y || 0})`);
    }

    const rot = t.rotation?.value as number | undefined;
    if (rot) {
      transforms.push(`rotate(${rot})`);
    }

    const scale = t.scale?.value as { x?: number; y?: number } | undefined;
    if (scale && (scale.x !== 100 || scale.y !== 100)) {
      transforms.push(
        `scale(${(scale.x || 100) / 100},${(scale.y || 100) / 100})`,
      );
    }

    return transforms.join(" ");
  }

  private calculateBounds(points: ControlPoint[]) {
    if (points.length === 0) return { minX: 0, minY: 0, maxX: 0, maxY: 0 };
    let minX = Infinity,
      minY = Infinity,
      maxX = -Infinity,
      maxY = -Infinity;
    for (const p of points) {
      minX = Math.min(minX, p.x);
      minY = Math.min(minY, p.y);
      maxX = Math.max(maxX, p.x);
      maxY = Math.max(maxY, p.y);
    }
    return { minX, minY, maxX, maxY };
  }

  private sanitizeId(id: string): string {
    return id.replace(/[^a-zA-Z0-9_-]/g, "_");
  }
}

export const svgExportService = new SVGExportService();

export function exportSplineLayerToSVG(
  layer: Layer,
  options?: SVGExportOptions,
): SVGExportResult {
  return svgExportService.exportSplineLayer(layer, options);
}

export function exportCompositionToSVG(
  composition: { settings: { width: number; height: number } },
  layers: Layer[],
  options?: SVGExportOptions,
): SVGExportResult {
  return svgExportService.exportComposition(composition, layers, options);
}

export function controlPointsToPathData(
  points: ControlPoint[],
  closed: boolean,
  precision?: number,
): string {
  return svgExportService.controlPointsToPathData(points, closed, precision);
}

/**
 * Simple export for a single spline layer - returns SVG string
 */
export function exportSplineLayer(
  layer: Layer,
  options?: SVGExportOptions,
): string {
  return svgExportService.exportSplineLayer(layer, options).svg;
}

/**
 * Simple export for multiple layers - returns SVG string
 */
export function exportLayers(
  layers: Layer[],
  options?: SVGExportOptions,
): string {
  const composition = {
    settings: {
      width: options?.viewBox?.width ?? 1920,
      height: options?.viewBox?.height ?? 1080,
    },
  };
  return svgExportService.exportComposition(composition, layers, options).svg;
}

export default svgExportService;
