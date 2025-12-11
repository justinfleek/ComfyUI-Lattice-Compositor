import requests
import webbrowser
import json
from .utils import tensor_to_b64, tensor_batch_to_b64_list

BRIDGE_URL = "http://localhost:8765"

class WeylCompositorInput:
    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "images": ("IMAGE",),
                "depth_map": ("IMAGE",),
            },
            "optional": {
                "confidence": ("IMAGE",),
            }
        }

    RETURN_TYPES = ("WEYL_SESSION",)
    RETURN_NAMES = ("session",)
    FUNCTION = "send_to_compositor"
    CATEGORY = "Weyl"

    def send_to_compositor(self, images, depth_map, confidence=None):
        payload = {
            "frames": tensor_batch_to_b64_list(images),
            "depth": tensor_to_b64(depth_map),
            "resolution": [images.shape[2], images.shape[1]],
        }

        if confidence is not None:
            payload["confidence"] = tensor_to_b64(confidence)

        try:
            resp = requests.post(f"{BRIDGE_URL}/api/source", json=payload, timeout=30)
            resp.raise_for_status()
            session = resp.json()
            print(f"[Weyl] Source loaded, session: {session['session_id']}")
        except requests.exceptions.ConnectionError:
            print("[Weyl] Bridge not running, opening compositor...")
            webbrowser.open("http://localhost:8766")
            raise Exception(
                "Weyl Compositor is not running.\n"
                "1. Start the bridge: cd server && python main.py\n"
                "2. Open http://localhost:8766\n"
                "3. Re-run this node"
            )
        except Exception as e:
            raise Exception(f"Failed to send to compositor: {e}")

        return ({"session_id": session["session_id"], "bridge_url": BRIDGE_URL},)


class WeylCompositorOutput:
    @classmethod
    def INPUT_TYPES(cls):
        return {
            "required": {
                "session": ("WEYL_SESSION",),
            }
        }

    RETURN_TYPES = ("STRING", "INT")
    RETURN_NAMES = ("splines_json", "frame_count")
    FUNCTION = "receive_from_compositor"
    CATEGORY = "Weyl"

    def receive_from_compositor(self, session):
        bridge_url = session.get("bridge_url", BRIDGE_URL)

        try:
            resp = requests.get(f"{bridge_url}/api/export", timeout=10)
            resp.raise_for_status()
            data = resp.json()
        except Exception as e:
            raise Exception(f"Failed to get export from compositor: {e}")

        splines_json = json.dumps(data["splines"], indent=2)
        frame_count = data["frame_count"]

        print(f"[Weyl] Received {len(data['splines'])} splines, {frame_count} frames")

        return (splines_json, frame_count)
