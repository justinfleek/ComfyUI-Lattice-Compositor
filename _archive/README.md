# Weyl Compositor

A standalone motion graphics app that bridges to ComfyUI for AI video generation.

## Prerequisites
- Python 3.10+
- Node.js 18+
- ComfyUI installation

## Installation

### 1. Install Backend
```bash
cd server
pip install -r requirements.txt
```

### 2. Install Frontend
```bash
cd frontend
npm install
```

### 3. Install ComfyUI Nodes
Copy the `comfyui_nodes` folder to your ComfyUI custom_nodes directory:
```bash
cp -r comfyui_nodes /path/to/ComfyUI/custom_nodes/weyl_compositor
```

## Running

### Terminal 1: Backend Server
```bash
cd server
python main.py
# Runs on http://localhost:8765
```

### Terminal 2: Frontend Dev Server
```bash
cd frontend
npm run dev
# Runs on http://localhost:8766
```

## Usage

1. In ComfyUI, load an image and generate a depth map
2. Connect image + depth to **Weyl Compositor Input** node
3. Run the node - browser opens with compositor
4. Use Pen tool (P) to draw splines by clicking on the depth surface
5. Press Enter or click "Finish Spline" to complete a spline
6. Click "Export to ComfyUI"
7. Connect the session to **Weyl Compositor Output** node
8. Run to get your splines as JSON

## Keyboard Shortcuts
- V: Select tool
- P: Pen tool
- H: Hand tool
- Enter: Finish current spline
- Escape: Cancel current spline
