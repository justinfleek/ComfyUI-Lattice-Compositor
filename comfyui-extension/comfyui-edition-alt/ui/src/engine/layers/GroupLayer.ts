/**
 * GroupLayer - Layer Folder/Group
 *
 * A container layer that groups child layers together.
 * Similar to precomp functionality but without creating a separate composition.
 *
 * Features:
 * - Collapsed/expanded state in timeline
 * - Color labels
 * - Pass-through mode (no intermediate composite)
 * - Group isolation for editing
 *
 * DETERMINISM: Group transforms applied to children deterministically
 */

import * as THREE from "three";
import type { GroupLayerData, Layer } from "@/types/project";
import { BaseLayer } from "./BaseLayer";

export class GroupLayer extends BaseLayer {
  private groupData: GroupLayerData;
  private boundingBox: THREE.LineSegments | null = null;
  private labelMesh: THREE.Mesh | null = null;

  constructor(layerData: Layer) {
    super(layerData);
    this.groupData = this.extractGroupData(layerData);
    this.createVisuals();
  }

  /**
   * Extract group layer data from layer object
   */
  private extractGroupData(layerData: Layer): GroupLayerData {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
    const data = layerData.data as Partial<GroupLayerData> | undefined;
    const collapsed = (data !== null && data !== undefined && typeof data === "object" && "collapsed" in data && typeof data.collapsed === "boolean") ? data.collapsed : false;
    const color = (data !== null && data !== undefined && typeof data === "object" && "color" in data && typeof data.color === "string" && data.color.length > 0) ? data.color : "#888888";
    const passThrough = (data !== null && data !== undefined && typeof data === "object" && "passThrough" in data && typeof data.passThrough === "boolean") ? data.passThrough : true;
    const isolate = (data !== null && data !== undefined && typeof data === "object" && "isolate" in data && typeof data.isolate === "boolean") ? data.isolate : false;
    return {
      collapsed,
      color,
      passThrough,
      isolate,
    };
  }

  private createVisuals(): void {
    // Create group indicator (visible only in editor, not render)
    this.createBoundingBox();
    this.createLabel();
  }

  private createBoundingBox(): void {
    // Dashed bounding box to show group bounds
    const geometry = new THREE.BufferGeometry();
    const positions = new Float32Array([
      -50, -50, 0, 50, -50, 0, 50, -50, 0, 50, 50, 0, 50, 50, 0, -50, 50, 0,
      -50, 50, 0, -50, -50, 0,
    ]);
    geometry.setAttribute("position", new THREE.BufferAttribute(positions, 3));

    const material = new THREE.LineDashedMaterial({
      color: this.getGroupColor(),
      dashSize: 5,
      gapSize: 3,
      transparent: true,
      opacity: 0.5,
    });

    this.boundingBox = new THREE.LineSegments(geometry, material);
    this.boundingBox.computeLineDistances();
    this.boundingBox.name = `group_bounds_${this.id}`;
    this.group.add(this.boundingBox);
  }

  private createLabel(): void {
    // Simple label indicator at top-left of group
    const geometry = new THREE.PlaneGeometry(20, 20);
    const material = new THREE.MeshBasicMaterial({
      color: this.getGroupColor(),
      transparent: true,
      opacity: 0.7,
    });

    this.labelMesh = new THREE.Mesh(geometry, material);
    this.labelMesh.position.set(-40, 40, 0);
    this.labelMesh.name = `group_label_${this.id}`;
    this.group.add(this.labelMesh);
  }

  private getGroupColor(): number {
    if (this.groupData.color) {
      return parseInt(this.groupData.color.replace("#", ""), 16);
    }
    return 0x888888; // Default gray
  }

  // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
  //                                               // abstract // implementations
  // ════════════════════════════════════════════════════════════════════════════

  protected onEvaluateFrame(_frame: number): void {
    // Group layer's transform is applied to the container,
    // which affects all child layers that reference this as parent

    // Update visuals based on data
    if (this.boundingBox) {
      const material = this.boundingBox.material as THREE.LineDashedMaterial;
      material.color.setHex(this.getGroupColor());
    }

    if (this.labelMesh) {
      const material = this.labelMesh.material as THREE.MeshBasicMaterial;
      material.color.setHex(this.getGroupColor());
    }
  }

  protected onUpdate(properties: Partial<Layer>): void {
    const data = properties.data as Partial<GroupLayerData> | undefined;

    if (data) {
      Object.assign(this.groupData, data);
    }
  }

  protected onDispose(): void {
    if (this.boundingBox) {
      this.boundingBox.geometry.dispose();
      (this.boundingBox.material as THREE.Material).dispose();
    }

    if (this.labelMesh) {
      this.labelMesh.geometry.dispose();
      (this.labelMesh.material as THREE.Material).dispose();
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // group
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Update the group's bounding box based on child layer bounds
   */
  updateBoundsFromChildren(childBounds: THREE.Box3): void {
    if (!this.boundingBox) return;

    const size = childBounds.getSize(new THREE.Vector3());
    const center = childBounds.getCenter(new THREE.Vector3());

    // Update bounding box geometry
    const halfX = size.x / 2;
    const halfY = size.y / 2;

    const positions = new Float32Array([
      -halfX,
      -halfY,
      0,
      halfX,
      -halfY,
      0,
      halfX,
      -halfY,
      0,
      halfX,
      halfY,
      0,
      halfX,
      halfY,
      0,
      -halfX,
      halfY,
      0,
      -halfX,
      halfY,
      0,
      -halfX,
      -halfY,
      0,
    ]);

    this.boundingBox.geometry.setAttribute(
      "position",
      new THREE.BufferAttribute(positions, 3),
    );
    this.boundingBox.geometry.attributes.position.needsUpdate = true;
    this.boundingBox.computeLineDistances();
    this.boundingBox.position.copy(center);
  }

  /**
   * Check if group is in pass-through mode
   * In pass-through, group doesn't create intermediate composite
   */
  isPassThrough(): boolean {
    return this.groupData.passThrough;
  }

  /**
   * Check if group is isolated (only show group contents)
   */
  isIsolated(): boolean {
    return this.groupData.isolate;
  }

  /**
   * Check if group is collapsed in timeline
   */
  isCollapsed(): boolean {
    return this.groupData.collapsed;
  }

  /**
   * Toggle collapsed state
   */
  toggleCollapsed(): void {
    this.groupData.collapsed = !this.groupData.collapsed;
  }
}
