import * as THREE from 'three';

export function createDepthMesh(
  depthData: Uint8Array,
  width: number,
  height: number,
  colorTexture?: THREE.Texture
): THREE.Mesh {
  const segmentsX = Math.min(width, 256);
  const segmentsY = Math.min(height, 256);

  const geometry = new THREE.PlaneGeometry(
    width / 100,
    height / 100,
    segmentsX,
    segmentsY
  );

  const positions = geometry.attributes.position;
  const depthScale = 2;

  for (let i = 0; i < positions.count; i++) {
    const x = positions.getX(i);
    const y = positions.getY(i);

    const u = (x / (width / 100) + 0.5);
    const v = (y / (height / 100) + 0.5);

    const px = Math.floor(u * width);
    const py = Math.floor((1 - v) * height);
    const idx = Math.min(py * width + px, depthData.length - 1);
    const depth = depthData[idx] / 255;

    positions.setZ(i, (1 - depth) * depthScale);
  }

  geometry.computeVertexNormals();

  const material = new THREE.MeshStandardMaterial({
    map: colorTexture || null,
    color: colorTexture ? 0xffffff : 0x888888,
    side: THREE.DoubleSide,
    wireframe: false,
  });

  const mesh = new THREE.Mesh(geometry, material);
  mesh.rotation.x = -Math.PI / 2;

  return mesh;
}

export function updateDepthMeshTexture(mesh: THREE.Mesh, texture: THREE.Texture) {
  const material = mesh.material as THREE.MeshStandardMaterial;
  material.map = texture;
  material.needsUpdate = true;
}
