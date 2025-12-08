const API_BASE = '/api';

export interface SourceInfo {
  frame_count: number;
  resolution: [number, number];
  has_depth: boolean;
}

export interface StatusResponse {
  ready: boolean;
  has_source: boolean;
  frame_count: number;
  resolution: [number, number];
  spline_count: number;
}

export async function getStatus(): Promise<StatusResponse> {
  const resp = await fetch(`${API_BASE}/status`);
  return resp.json();
}

export async function getSourceInfo(): Promise<SourceInfo> {
  const resp = await fetch(`${API_BASE}/source/info`);
  return resp.json();
}

export async function getFrame(index: number): Promise<string> {
  const resp = await fetch(`${API_BASE}/source/frame/${index}`);
  const data = await resp.json();
  return data.frame;
}

export async function getDepthMap(): Promise<string> {
  const resp = await fetch(`${API_BASE}/source/depth`);
  const data = await resp.json();
  return data.depth;
}

export async function sampleDepth(x: number, y: number): Promise<number> {
  const resp = await fetch(`${API_BASE}/depth/sample?x=${Math.round(x)}&y=${Math.round(y)}`);
  const data = await resp.json();
  return data.z;
}

export async function addSpline(spline: any): Promise<void> {
  await fetch(`${API_BASE}/spline`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(spline),
  });
}

export async function getSplines(): Promise<any[]> {
  const resp = await fetch(`${API_BASE}/splines`);
  const data = await resp.json();
  return data.splines;
}

export async function clearSplines(): Promise<void> {
  await fetch(`${API_BASE}/splines`, { method: 'DELETE' });
}

export async function exportData(): Promise<any> {
  const resp = await fetch(`${API_BASE}/export`);
  return resp.json();
}
