import * as THREE from 'three';
import { Spline, SplinePoint } from '../types/Spline';

export function createSplineMesh(spline: Spline, color: number = 0x00ff00): THREE.Line {
  const points = spline.points.map(p =>
    new THREE.Vector3(
      (p.x / 100) - 9.6,
      (1 - p.z) * 2 + 0.1,
      (p.y / 100) - 5.4
    )
  );

  const geometry = new THREE.BufferGeometry().setFromPoints(points);
  const material = new THREE.LineBasicMaterial({ color, linewidth: 2 });

  return new THREE.Line(geometry, material);
}

export function createPointMarkers(points: SplinePoint[], color: number = 0xffff00): THREE.Points {
  const positions = points.map(p =>
    new THREE.Vector3(
      (p.x / 100) - 9.6,
      (1 - p.z) * 2 + 0.1,
      (p.y / 100) - 5.4
    )
  );

  const geometry = new THREE.BufferGeometry().setFromPoints(positions);
  const material = new THREE.PointsMaterial({ color, size: 0.2 });

  return new THREE.Points(geometry, material);
}
