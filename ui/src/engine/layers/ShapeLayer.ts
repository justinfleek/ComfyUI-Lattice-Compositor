/**
 * ShapeLayer - Vector Shape Layer Implementation
 *
 * Professional vector shape layer features:
 * - Shape generators (rectangle, ellipse, polygon, star, path)
 * - Path operators (trim paths, merge paths, offset, pucker/bloat, wiggle, etc.)
 * - Fill and stroke with gradient support
 * - Repeater with transform
 * - Group hierarchy
 * - Path simplification
 * - Image trace (vectorization)
 * - Extrude (3D)
 */

import * as THREE from 'three';
import { BaseLayer } from './BaseLayer';
import type { Layer } from '@/types/project';
import type {
  ShapeLayerData,
  ShapeContent,
  ShapeGroup,
  ShapeGenerator,
  ShapeModifier,
  PathOperator,
  ShapeTransform,
  RepeaterOperator,
  BezierPath,
  BezierVertex,
  Point2D,
  ShapeColor,
  FillShape,
  StrokeShape,
  GradientFillShape,
  GradientStrokeShape,
  TrimPathsOperator,
  MergePathsOperator,
  OffsetPathsOperator,
  PuckerBloatOperator,
  WigglePathsOperator,
  ZigZagOperator,
  TwistOperator,
  RoundedCornersOperator,
  RectangleShape,
  EllipseShape,
  PolygonShape,
  StarShape,
  PathShape,
  ExtrudeOperator,
  SimplifyPathOperator,
  SmoothPathOperator,
  IllustratorOperator,
} from '@/types/shapes';
import {
  ShapeOperations,
  generateRectangle,
  generateEllipse,
  generatePolygon,
  generateStar,
  trimPath,
  mergePaths,
  offsetPath,
  puckerBloat,
  wigglePath,
  zigZagPath,
  twistPath,
  roundCorners,
  simplifyPath,
  smoothPath,
  applyRepeater,
  transformPath,
  clonePath,
} from '@/services/shapeOperations';
import { layerLogger } from '@/utils/logger';
import { interpolateProperty } from '@/services/interpolation';
import type { AnimatableProperty } from '@/types/project';

// ============================================================================
// EVALUATED SHAPE STATE
// ============================================================================

interface EvaluatedPath {
  path: BezierPath;
  fill?: {
    color: ShapeColor;
    opacity: number;
    rule: 'nonzero' | 'evenodd';
  };
  stroke?: {
    color: ShapeColor;
    opacity: number;
    width: number;
    lineCap: string;
    lineJoin: string;
    dashPattern: number[];
    dashOffset: number;
  };
  gradientFill?: {
    type: 'linear' | 'radial';
    stops: Array<{ position: number; color: ShapeColor }>;
    startPoint: Point2D;
    endPoint: Point2D;
    opacity: number;
  };
}

// ============================================================================
// SHAPE LAYER CLASS
// ============================================================================

export class ShapeLayer extends BaseLayer {
  public readonly type = 'shape' as const;

  // Shape data
  private shapeData: ShapeLayerData;

  // Rendering
  private canvas: OffscreenCanvas;
  private ctx: OffscreenCanvasRenderingContext2D;
  private texture: THREE.CanvasTexture;
  private mesh: THREE.Mesh;

  // Canvas size (matches composition)
  private canvasWidth: number = 1920;
  private canvasHeight: number = 1080;

  // 3D extrusion (if any)
  private extrudedMeshes: THREE.Mesh[] = [];
  private extrudeGroup: THREE.Group;

  // Current frame for animation
  private currentFrame: number = 0;

  constructor(layerData: Layer) {
    super(layerData);

    // Get shape data from layer
    this.shapeData = (layerData.data as ShapeLayerData) || {
      contents: [],
      blendMode: 'normal',
      quality: 'normal',
      gpuAccelerated: true,
    };

    // Create canvas for rendering
    this.canvas = new OffscreenCanvas(this.canvasWidth, this.canvasHeight);
    this.ctx = this.canvas.getContext('2d')!;

    // Create texture
    this.texture = new THREE.CanvasTexture(this.canvas as any);
    this.texture.colorSpace = THREE.SRGBColorSpace;
    this.texture.minFilter = THREE.LinearFilter;
    this.texture.magFilter = THREE.LinearFilter;

    // Create mesh
    const geometry = new THREE.PlaneGeometry(this.canvasWidth, this.canvasHeight);
    const material = new THREE.MeshBasicMaterial({
      map: this.texture,
      transparent: true,
      side: THREE.DoubleSide,
    });

    this.mesh = new THREE.Mesh(geometry, material);
    this.mesh.position.set(this.canvasWidth / 2, this.canvasHeight / 2, 0);
    this.group.add(this.mesh);

    // Create extrude group for 3D shapes
    this.extrudeGroup = new THREE.Group();
    this.group.add(this.extrudeGroup);

    // Initial render
    this.renderShape();
  }

  // ============================================================================
  // SIZE MANAGEMENT
  // ============================================================================

  /**
   * Set canvas size (should match composition)
   */
  setSize(width: number, height: number): void {
    if (width === this.canvasWidth && height === this.canvasHeight) return;

    this.canvasWidth = width;
    this.canvasHeight = height;

    // Recreate canvas
    this.canvas = new OffscreenCanvas(width, height);
    this.ctx = this.canvas.getContext('2d')!;

    // Update texture
    this.texture.image = this.canvas as any;
    this.texture.needsUpdate = true;

    // Update mesh geometry
    this.mesh.geometry.dispose();
    this.mesh.geometry = new THREE.PlaneGeometry(width, height);
    this.mesh.position.set(width / 2, height / 2, 0);

    this.renderShape();
  }

  // ============================================================================
  // SHAPE DATA ACCESS
  // ============================================================================

  getShapeData(): ShapeLayerData {
    return this.shapeData;
  }

  setShapeData(data: ShapeLayerData): void {
    this.shapeData = data;
    this.renderShape();
  }

  addContent(content: ShapeContent): void {
    this.shapeData.contents.push(content);
    this.renderShape();
  }

  removeContent(index: number): void {
    this.shapeData.contents.splice(index, 1);
    this.renderShape();
  }

  updateContent(index: number, content: ShapeContent): void {
    if (index >= 0 && index < this.shapeData.contents.length) {
      this.shapeData.contents[index] = content;
      this.renderShape();
    }
  }

  // ============================================================================
  // FRAME EVALUATION
  // ============================================================================

  evaluateFrame(frame: number): void {
    this.currentFrame = frame;
    super.evaluateFrame(frame);
    this.renderShape();
  }

  /**
   * Called during frame evaluation to update shape-specific properties
   */
  protected onEvaluateFrame(frame: number): void {
    // Shape layers re-render on every frame to handle animated shape properties
    // The actual rendering is done in renderShape() called from evaluateFrame()
    this.currentFrame = frame;
  }

  /**
   * Called when layer properties are updated
   */
  protected onUpdate(properties: Partial<Layer>): void {
    // Check for shape data updates
    if (properties.data) {
      this.shapeData = properties.data as ShapeLayerData;
      this.renderShape();
    }
  }

  onApplyEvaluatedState(state: any): void {
    // Shape-specific state could include animated shape properties
    if (state.shapeData) {
      this.shapeData = state.shapeData;
    }
    this.renderShape();
  }

  // ============================================================================
  // SHAPE RENDERING
  // ============================================================================

  /**
   * Main render function
   */
  private renderShape(): void {
    // Clear canvas
    this.ctx.clearRect(0, 0, this.canvasWidth, this.canvasHeight);

    // Process contents
    const evaluatedPaths = this.evaluateContents(this.shapeData.contents);

    // Render all paths
    for (const evalPath of evaluatedPaths) {
      this.renderPath(evalPath);
    }

    // Update texture
    this.texture.needsUpdate = true;
  }

  /**
   * Evaluate all shape contents into renderable paths
   */
  private evaluateContents(contents: ShapeContent[]): EvaluatedPath[] {
    // Collect generators, operators, and modifiers
    const generators: ShapeGenerator[] = [];
    const operators: PathOperator[] = [];
    const modifiers: ShapeModifier[] = [];
    const repeaters: RepeaterOperator[] = [];
    const transforms: ShapeTransform[] = [];
    const groups: ShapeGroup[] = [];
    const illustratorOps: IllustratorOperator[] = [];

    for (const content of contents) {
      switch (content.type) {
        case 'rectangle':
        case 'ellipse':
        case 'polygon':
        case 'star':
        case 'path':
          generators.push(content as ShapeGenerator);
          break;
        case 'fill':
        case 'stroke':
        case 'gradientFill':
        case 'gradientStroke':
          modifiers.push(content as ShapeModifier);
          break;
        case 'trimPaths':
        case 'mergePaths':
        case 'offsetPaths':
        case 'puckerBloat':
        case 'wigglePaths':
        case 'zigZag':
        case 'twist':
        case 'roundedCorners':
          operators.push(content as PathOperator);
          break;
        case 'repeater':
          repeaters.push(content as RepeaterOperator);
          break;
        case 'transform':
          transforms.push(content as ShapeTransform);
          break;
        case 'group':
          groups.push(content as ShapeGroup);
          break;
        case 'simplifyPath':
        case 'smoothPath':
        case 'extrude':
        case 'trace':
          illustratorOps.push(content as IllustratorOperator);
          break;
      }
    }

    // Generate base paths
    let paths: BezierPath[] = generators.map(gen => this.generatePath(gen));

    // Apply path operators in order
    for (const op of operators) {
      paths = this.applyOperator(paths, op);
    }

    // Apply Illustrator operators
    for (const op of illustratorOps) {
      paths = this.applyIllustratorOperator(paths, op);
    }

    // Apply transforms
    for (const transform of transforms) {
      paths = paths.map(p => this.applyShapeTransform(p, transform));
    }

    // Apply repeaters
    for (const repeater of repeaters) {
      paths = this.applyRepeater(paths, repeater);
    }

    // Create evaluated paths with fill/stroke info
    const result: EvaluatedPath[] = [];

    for (const path of paths) {
      const evalPath: EvaluatedPath = { path };

      // Apply modifiers
      for (const mod of modifiers) {
        this.applyModifier(evalPath, mod);
      }

      result.push(evalPath);
    }

    // Process nested groups recursively
    for (const group of groups) {
      const groupPaths = this.evaluateContents(group.contents);
      result.push(...groupPaths);
    }

    return result;
  }

  /**
   * Generate a path from a shape generator
   */
  private generatePath(generator: ShapeGenerator): BezierPath {
    switch (generator.type) {
      case 'rectangle': {
        const rect = generator as RectangleShape;
        const pos = this.getAnimatedValue(rect.position);
        const size = this.getAnimatedValue(rect.size);
        const roundness = this.getAnimatedValue(rect.roundness);
        return generateRectangle(pos, size, roundness, rect.direction);
      }

      case 'ellipse': {
        const ellipse = generator as EllipseShape;
        const pos = this.getAnimatedValue(ellipse.position);
        const size = this.getAnimatedValue(ellipse.size);
        return generateEllipse(pos, size, ellipse.direction);
      }

      case 'polygon': {
        const poly = generator as PolygonShape;
        const pos = this.getAnimatedValue(poly.position);
        const points = this.getAnimatedValue(poly.points);
        const radius = this.getAnimatedValue(poly.outerRadius);
        const roundness = this.getAnimatedValue(poly.outerRoundness);
        const rotation = this.getAnimatedValue(poly.rotation);
        return generatePolygon(pos, points, radius, roundness, rotation, poly.direction);
      }

      case 'star': {
        const star = generator as StarShape;
        const pos = this.getAnimatedValue(star.position);
        const points = this.getAnimatedValue(star.points);
        const outerR = this.getAnimatedValue(star.outerRadius);
        const innerR = this.getAnimatedValue(star.innerRadius);
        const outerRound = this.getAnimatedValue(star.outerRoundness);
        const innerRound = this.getAnimatedValue(star.innerRoundness);
        const rotation = this.getAnimatedValue(star.rotation);
        return generateStar(pos, points, outerR, innerR, outerRound, innerRound, rotation, star.direction);
      }

      case 'path': {
        const pathShape = generator as PathShape;
        return clonePath(this.getAnimatedValue(pathShape.path));
      }

      default:
        return { vertices: [], closed: false };
    }
  }

  /**
   * Apply a path operator to paths
   */
  private applyOperator(paths: BezierPath[], operator: PathOperator): BezierPath[] {
    switch (operator.type) {
      case 'trimPaths': {
        const trim = operator as TrimPathsOperator;
        const start = this.getAnimatedValue(trim.start);
        const end = this.getAnimatedValue(trim.end);
        const offset = this.getAnimatedValue(trim.offset);

        if (trim.mode === 'simultaneously') {
          return paths.map(p => trimPath(p, start, end, offset));
        } else {
          // Individually - trim each path based on its index
          return paths.map((p, i) => {
            const pathStart = (start + (100 / paths.length) * i) % 100;
            const pathEnd = (end + (100 / paths.length) * i) % 100;
            return trimPath(p, pathStart, pathEnd, offset);
          });
        }
      }

      case 'mergePaths': {
        const merge = operator as MergePathsOperator;
        return mergePaths(paths, merge.mode);
      }

      case 'offsetPaths': {
        const offset = operator as OffsetPathsOperator;
        const amount = this.getAnimatedValue(offset.amount);
        const copies = this.getAnimatedValue(offset.copies);
        const copyOff = this.getAnimatedValue(offset.copyOffset);
        const miter = this.getAnimatedValue(offset.miterLimit);

        if (copies <= 1) {
          return paths.map(p => offsetPath(p, amount, offset.lineJoin, miter));
        } else {
          return paths.flatMap(p =>
            ShapeOperations.offsetPathMultiple(p, amount, copies, copyOff, offset.lineJoin, miter)
          );
        }
      }

      case 'puckerBloat': {
        const pb = operator as PuckerBloatOperator;
        const amount = this.getAnimatedValue(pb.amount);
        return paths.map(p => puckerBloat(p, amount));
      }

      case 'wigglePaths': {
        const wiggle = operator as WigglePathsOperator;
        const size = this.getAnimatedValue(wiggle.size);
        const detail = this.getAnimatedValue(wiggle.detail);
        const correlation = this.getAnimatedValue(wiggle.correlation);
        const temporal = this.getAnimatedValue(wiggle.temporalPhase) + this.currentFrame * 0.1;
        const spatial = this.getAnimatedValue(wiggle.spatialPhase);

        return paths.map((p, i) =>
          wigglePath(p, size, detail, wiggle.points, correlation, temporal, spatial, wiggle.randomSeed + i)
        );
      }

      case 'zigZag': {
        const zz = operator as ZigZagOperator;
        const size = this.getAnimatedValue(zz.size);
        const ridges = this.getAnimatedValue(zz.ridgesPerSegment);
        return paths.map(p => zigZagPath(p, size, ridges, zz.points));
      }

      case 'twist': {
        const twist = operator as TwistOperator;
        const angle = this.getAnimatedValue(twist.angle);
        const center = this.getAnimatedValue(twist.center);
        return paths.map(p => twistPath(p, angle, center));
      }

      case 'roundedCorners': {
        const rc = operator as RoundedCornersOperator;
        const radius = this.getAnimatedValue(rc.radius);
        return paths.map(p => roundCorners(p, radius));
      }

      default:
        return paths;
    }
  }

  /**
   * Apply Illustrator-specific operators
   */
  private applyIllustratorOperator(paths: BezierPath[], operator: IllustratorOperator): BezierPath[] {
    switch (operator.type) {
      case 'simplifyPath': {
        const simp = operator as SimplifyPathOperator;
        const tolerance = this.getAnimatedValue(simp.tolerance);
        return paths.map(p => simplifyPath(p, tolerance, simp.straightLines));
      }

      case 'smoothPath': {
        const smooth = operator as SmoothPathOperator;
        const amount = this.getAnimatedValue(smooth.amount);
        return paths.map(p => smoothPath(p, amount));
      }

      case 'extrude': {
        // Extrude creates 3D geometry, handled separately
        this.createExtrudedGeometry(paths, operator as ExtrudeOperator);
        return paths;
      }

      case 'trace': {
        // Trace is handled at a higher level (needs image source)
        return paths;
      }

      default:
        return paths;
    }
  }

  /**
   * Apply a shape transform
   */
  private applyShapeTransform(path: BezierPath, transform: ShapeTransform): BezierPath {
    const anchor = this.getAnimatedValue(transform.anchorPoint);
    const position = this.getAnimatedValue(transform.position);
    const scale = this.getAnimatedValue(transform.scale);
    const rotation = this.getAnimatedValue(transform.rotation);

    return transformPath(path, anchor, position, scale, rotation);
  }

  /**
   * Apply repeater operator
   */
  private applyRepeater(paths: BezierPath[], repeater: RepeaterOperator): BezierPath[] {
    const copies = Math.floor(this.getAnimatedValue(repeater.copies));
    if (copies <= 1) return paths;

    const offset = this.getAnimatedValue(repeater.offset);
    const anchor = this.getAnimatedValue(repeater.transform.anchorPoint);
    const position = this.getAnimatedValue(repeater.transform.position);
    const scale = this.getAnimatedValue(repeater.transform.scale);
    const rotation = this.getAnimatedValue(repeater.transform.rotation);
    const startOp = this.getAnimatedValue(repeater.transform.startOpacity);
    const endOp = this.getAnimatedValue(repeater.transform.endOpacity);

    const repeated = applyRepeater(
      paths, copies, offset, anchor, position, scale, rotation, startOp, endOp
    );

    // Flatten the results (ignoring opacity for now - would need per-path opacity)
    const result: BezierPath[] = [];
    if (repeater.composite === 'below') {
      // Original first, then copies
      result.push(...paths);
      for (const rep of repeated.slice(1)) {
        result.push(...rep.paths);
      }
    } else {
      // Copies first, then original
      for (let i = repeated.length - 1; i >= 1; i--) {
        result.push(...repeated[i].paths);
      }
      result.push(...paths);
    }

    return result;
  }

  /**
   * Apply a modifier (fill/stroke) to an evaluated path
   */
  private applyModifier(evalPath: EvaluatedPath, modifier: ShapeModifier): void {
    switch (modifier.type) {
      case 'fill': {
        const fill = modifier as FillShape;
        evalPath.fill = {
          color: this.getAnimatedValue(fill.color),
          opacity: this.getAnimatedValue(fill.opacity),
          rule: fill.fillRule,
        };
        break;
      }

      case 'stroke': {
        const stroke = modifier as StrokeShape;
        evalPath.stroke = {
          color: this.getAnimatedValue(stroke.color),
          opacity: this.getAnimatedValue(stroke.opacity),
          width: this.getAnimatedValue(stroke.width),
          lineCap: stroke.lineCap,
          lineJoin: stroke.lineJoin,
          dashPattern: this.getAnimatedValue(stroke.dashPattern),
          dashOffset: this.getAnimatedValue(stroke.dashOffset),
        };
        break;
      }

      case 'gradientFill': {
        const grad = modifier as GradientFillShape;
        const gradDef = this.getAnimatedValue(grad.gradient);
        evalPath.gradientFill = {
          type: gradDef.type,
          stops: gradDef.stops,
          startPoint: gradDef.startPoint,
          endPoint: gradDef.endPoint,
          opacity: this.getAnimatedValue(grad.opacity),
        };
        break;
      }

      case 'gradientStroke': {
        // Similar to gradientFill but for stroke
        // Would need additional stroke properties
        break;
      }
    }
  }

  /**
   * Get animated value at current frame using proper keyframe interpolation
   */
  private getAnimatedValue<T>(prop: AnimatableProperty<T>): T {
    // Use the interpolation service for proper keyframe interpolation
    // This handles all interpolation types (linear, bezier, hold) and expressions
    return interpolateProperty(prop, this.currentFrame, 30, this.layer.id);
  }

  /**
   * Render a single evaluated path to canvas
   */
  private renderPath(evalPath: EvaluatedPath): void {
    const { path, fill, stroke, gradientFill } = evalPath;

    if (path.vertices.length < 2) return;

    this.ctx.save();

    // Build Path2D
    const path2d = this.buildPath2D(path);

    // Fill
    if (gradientFill) {
      const gradient = this.createGradient(gradientFill);
      this.ctx.globalAlpha = gradientFill.opacity / 100;
      this.ctx.fillStyle = gradient;
      this.ctx.fill(path2d, 'nonzero');
    } else if (fill) {
      this.ctx.globalAlpha = fill.opacity / 100;
      this.ctx.fillStyle = this.colorToCSS(fill.color);
      this.ctx.fill(path2d, fill.rule);
    }

    // Stroke
    if (stroke && stroke.width > 0) {
      this.ctx.globalAlpha = stroke.opacity / 100;
      this.ctx.strokeStyle = this.colorToCSS(stroke.color);
      this.ctx.lineWidth = stroke.width;
      this.ctx.lineCap = stroke.lineCap as CanvasLineCap;
      this.ctx.lineJoin = stroke.lineJoin as CanvasLineJoin;

      if (stroke.dashPattern.length > 0) {
        this.ctx.setLineDash(stroke.dashPattern);
        this.ctx.lineDashOffset = stroke.dashOffset;
      }

      this.ctx.stroke(path2d);
    }

    this.ctx.restore();
  }

  /**
   * Build a Path2D from a BezierPath
   */
  private buildPath2D(path: BezierPath): Path2D {
    const p = new Path2D();

    if (path.vertices.length === 0) return p;

    const v0 = path.vertices[0];
    p.moveTo(v0.point.x, v0.point.y);

    for (let i = 0; i < path.vertices.length; i++) {
      const curr = path.vertices[i];
      const next = path.vertices[(i + 1) % path.vertices.length];

      if (!path.closed && i === path.vertices.length - 1) break;

      // Control points
      const cp1x = curr.point.x + curr.outHandle.x;
      const cp1y = curr.point.y + curr.outHandle.y;
      const cp2x = next.point.x + next.inHandle.x;
      const cp2y = next.point.y + next.inHandle.y;

      p.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, next.point.x, next.point.y);
    }

    if (path.closed) {
      p.closePath();
    }

    return p;
  }

  /**
   * Convert ShapeColor to CSS color string
   */
  private colorToCSS(color: ShapeColor): string {
    return `rgba(${color.r}, ${color.g}, ${color.b}, ${color.a})`;
  }

  /**
   * Create canvas gradient
   */
  private createGradient(gradDef: EvaluatedPath['gradientFill']): CanvasGradient {
    if (!gradDef) {
      return this.ctx.createLinearGradient(0, 0, 0, 0);
    }

    const startX = gradDef.startPoint.x * this.canvasWidth;
    const startY = gradDef.startPoint.y * this.canvasHeight;
    const endX = gradDef.endPoint.x * this.canvasWidth;
    const endY = gradDef.endPoint.y * this.canvasHeight;

    let gradient: CanvasGradient;

    if (gradDef.type === 'linear') {
      gradient = this.ctx.createLinearGradient(startX, startY, endX, endY);
    } else {
      const radius = Math.sqrt(
        Math.pow(endX - startX, 2) + Math.pow(endY - startY, 2)
      );
      gradient = this.ctx.createRadialGradient(startX, startY, 0, startX, startY, radius);
    }

    for (const stop of gradDef.stops) {
      gradient.addColorStop(stop.position, this.colorToCSS(stop.color));
    }

    return gradient;
  }

  /**
   * Create extruded 3D geometry from paths
   */
  private createExtrudedGeometry(paths: BezierPath[], extrude: ExtrudeOperator): void {
    // Clear existing extrusions
    for (const mesh of this.extrudedMeshes) {
      this.extrudeGroup.remove(mesh);
      mesh.geometry.dispose();
      (mesh.material as THREE.Material).dispose();
    }
    this.extrudedMeshes = [];

    const depth = this.getAnimatedValue(extrude.depth);
    const bevelDepth = this.getAnimatedValue(extrude.bevelDepth);
    const frontColor = this.getAnimatedValue(extrude.material.frontColor);
    const sideColor = this.getAnimatedValue(extrude.material.sideColor);

    for (const path of paths) {
      if (path.vertices.length < 3 || !path.closed) continue;

      // Create THREE.Shape from path
      const shape = new THREE.Shape();
      const v0 = path.vertices[0];
      shape.moveTo(v0.point.x, v0.point.y);

      for (let i = 0; i < path.vertices.length; i++) {
        const curr = path.vertices[i];
        const next = path.vertices[(i + 1) % path.vertices.length];

        const cp1x = curr.point.x + curr.outHandle.x;
        const cp1y = curr.point.y + curr.outHandle.y;
        const cp2x = next.point.x + next.inHandle.x;
        const cp2y = next.point.y + next.inHandle.y;

        shape.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, next.point.x, next.point.y);
      }

      // Create extruded geometry
      const geometry = new THREE.ExtrudeGeometry(shape, {
        depth,
        bevelEnabled: bevelDepth > 0,
        bevelThickness: bevelDepth,
        bevelSize: bevelDepth,
        bevelSegments: extrude.bevelSegments,
      });

      // Create material
      const material = new THREE.MeshStandardMaterial({
        color: new THREE.Color(frontColor.r / 255, frontColor.g / 255, frontColor.b / 255),
        metalness: 0.1,
        roughness: 0.8,
      });

      const mesh = new THREE.Mesh(geometry, material);
      this.extrudeGroup.add(mesh);
      this.extrudedMeshes.push(mesh);
    }
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  dispose(): void {
    // Dispose texture
    this.texture.dispose();

    // Dispose mesh
    this.mesh.geometry.dispose();
    (this.mesh.material as THREE.Material).dispose();

    // Dispose extrusions
    for (const mesh of this.extrudedMeshes) {
      mesh.geometry.dispose();
      (mesh.material as THREE.Material).dispose();
    }

    super.dispose();
  }
}

export default ShapeLayer;
