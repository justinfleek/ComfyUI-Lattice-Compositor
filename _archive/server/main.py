from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles
from fastapi.responses import JSONResponse
import os

from models import SourceData, Spline, SplinePoint, ExportData
from state import compositor

app = FastAPI(title="Weyl Compositor Bridge")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["http://localhost:8766", "http://127.0.0.1:8766"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

@app.get("/api/status")
async def get_status():
    return {
        "ready": True,
        "has_source": compositor.session_id is not None,
        "frame_count": len(compositor.frames),
        "resolution": list(compositor.resolution),
        "spline_count": len(compositor.splines),
    }

@app.post("/api/source")
async def load_source(data: SourceData):
    session_id = compositor.load_source(
        frames_b64=data.frames,
        depth_b64=data.depth,
        resolution=data.resolution,
        confidence_b64=data.confidence,
    )
    return {"session_id": session_id, "status": "loaded"}

@app.get("/api/source/frame/{index}")
async def get_frame(index: int):
    frame_b64 = compositor.get_frame_b64(index)
    if not frame_b64:
        raise HTTPException(404, "Frame not found")
    return {"frame": frame_b64}

@app.get("/api/source/depth")
async def get_depth():
    return {"depth": compositor.get_depth_b64()}

@app.get("/api/source/info")
async def get_source_info():
    return {
        "frame_count": len(compositor.frames),
        "resolution": list(compositor.resolution),
        "has_depth": compositor.depth_map is not None,
    }

@app.post("/api/spline")
async def add_spline(spline: Spline):
    compositor.add_spline(spline)
    return {"status": "added", "id": spline.id}

@app.get("/api/splines")
async def get_splines():
    return {"splines": [s.dict() for s in compositor.splines]}

@app.delete("/api/splines")
async def clear_splines():
    compositor.splines = []
    return {"status": "cleared"}

@app.get("/api/depth/sample")
async def sample_depth(x: int, y: int):
    z = compositor.get_depth_at(x, y)
    return {"x": x, "y": y, "z": z}

@app.get("/api/export")
async def export_data():
    return {
        "splines": [s.dict() for s in compositor.splines],
        "frame_count": len(compositor.frames),
        "resolution": list(compositor.resolution),
    }

frontend_path = os.path.join(os.path.dirname(__file__), "../frontend/dist")
if os.path.exists(frontend_path):
    app.mount("/", StaticFiles(directory=frontend_path, html=True), name="frontend")

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8765)
