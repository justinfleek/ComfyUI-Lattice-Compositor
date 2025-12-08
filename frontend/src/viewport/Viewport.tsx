import React, { useEffect, useRef, useState } from 'react';
import { Canvas, useThree, useFrame } from '@react-three/fiber';
import { OrbitControls, PerspectiveCamera } from '@react-three/drei';
import * as THREE from 'three';
import { useStore } from '../state/store';
import { getFrame, getDepthMap, sampleDepth, addSpline as apiAddSpline } from '../bridge/api';
import { createDepthMesh } from './DepthMesh';
import { createSplineMesh, createPointMarkers } from './SplineRenderer';

function Scene() {
  const { scene, camera, gl } = useThree();
  const [depthMesh, setDepthMesh] = useState<THREE.Mesh | null>(null);
  const splineMeshesRef = useRef<THREE.Line[]>([]);
  const pointMarkersRef = useRef<THREE.Points | null>(null);

  const {
    hasSource,
    resolution,
    currentFrame,
    activeTool,
    splines,
    currentSplinePoints,
    addPointToCurrentSpline,
    finishCurrentSpline,
  } = useStore();

  useEffect(() => {
    if (!hasSource) return;

    const loadDepth = async () => {
      try {
        const depthB64 = await getDepthMap();
        const depthImg = new Image();
        depthImg.src = `data:image/png;base64,${depthB64}`;

        await new Promise(resolve => depthImg.onload = resolve);

        const canvas = document.createElement('canvas');
        canvas.width = depthImg.width;
        canvas.height = depthImg.height;
        const ctx = canvas.getContext('2d')!;
        ctx.drawImage(depthImg, 0, 0);
        const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
        const depthData = new Uint8Array(canvas.width * canvas.height);
        for (let i = 0; i < depthData.length; i++) {
          depthData[i] = imageData.data[i * 4];
        }

        const frameB64 = await getFrame(currentFrame);
        const texture = new THREE.TextureLoader().load(`data:image/png;base64,${frameB64}`);

        const mesh = createDepthMesh(depthData, canvas.width, canvas.height, texture);

        if (depthMesh) {
          scene.remove(depthMesh);
        }

        scene.add(mesh);
        setDepthMesh(mesh);
      } catch (err) {
        console.error('Failed to load depth:', err);
      }
    };

    loadDepth();
  }, [hasSource, currentFrame]);

  useEffect(() => {
    splineMeshesRef.current.forEach(m => scene.remove(m));
    splineMeshesRef.current = [];

    splines.forEach(spline => {
      const mesh = createSplineMesh(spline);
      scene.add(mesh);
      splineMeshesRef.current.push(mesh);
    });
  }, [splines]);

  useEffect(() => {
    if (pointMarkersRef.current) {
      scene.remove(pointMarkersRef.current);
      pointMarkersRef.current = null;
    }

    if (currentSplinePoints.length > 0) {
      const markers = createPointMarkers(currentSplinePoints);
      scene.add(markers);
      pointMarkersRef.current = markers;

      if (currentSplinePoints.length > 1) {
        const tempSpline = { id: 'temp', points: currentSplinePoints, closed: false };
        const line = createSplineMesh(tempSpline, 0xff00ff);
        scene.add(line);
        splineMeshesRef.current.push(line);
      }
    }
  }, [currentSplinePoints]);

  const handleClick = async (event: THREE.Event) => {
    if (activeTool !== 'pen' || !hasSource || !depthMesh) return;

    const intersects = (event as any).intersections;
    if (intersects.length === 0) return;

    const hit = intersects[0];

    const x = (hit.point.x + 9.6) * 100;
    const y = (hit.point.z + 5.4) * 100;

    const z = await sampleDepth(x, y);

    addPointToCurrentSpline({ x, y, z });
  };

  return (
    <>
      <PerspectiveCamera makeDefault position={[0, 10, 10]} />
      <OrbitControls enableDamping dampingFactor={0.1} />
      <ambientLight intensity={0.5} />
      <directionalLight position={[10, 10, 5]} intensity={1} />
      <gridHelper args={[20, 20]} />
      <mesh onClick={handleClick} visible={false}>
        <planeGeometry args={[100, 100]} />
        <meshBasicMaterial transparent opacity={0} />
      </mesh>
    </>
  );
}

export default function Viewport() {
  const { hasSource } = useStore();

  if (!hasSource) {
    return (
      <div className="no-source">
        <h2>No Source Loaded</h2>
        <p>Send an image and depth map from ComfyUI using the WeylCompositorInput node.</p>
      </div>
    );
  }

  return (
    <Canvas>
      <Scene />
    </Canvas>
  );
}
