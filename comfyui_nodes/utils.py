import base64
import io
import numpy as np
from PIL import Image
import torch

def tensor_to_b64(tensor: torch.Tensor) -> str:
    if len(tensor.shape) == 4:
        tensor = tensor[0]

    arr = (tensor.cpu().numpy() * 255).astype(np.uint8)

    if arr.shape[-1] == 1:
        img = Image.fromarray(arr.squeeze(), mode='L')
    elif arr.shape[-1] == 3:
        img = Image.fromarray(arr, mode='RGB')
    elif arr.shape[-1] == 4:
        img = Image.fromarray(arr, mode='RGBA')
    else:
        raise ValueError(f"Unexpected channels: {arr.shape[-1]}")

    buf = io.BytesIO()
    img.save(buf, format='PNG')
    return base64.b64encode(buf.getvalue()).decode()

def tensor_batch_to_b64_list(tensor: torch.Tensor) -> list:
    result = []
    for i in range(tensor.shape[0]):
        result.append(tensor_to_b64(tensor[i:i+1]))
    return result

def b64_to_tensor(b64_string: str) -> torch.Tensor:
    img_bytes = base64.b64decode(b64_string)
    img = Image.open(io.BytesIO(img_bytes))
    arr = np.array(img).astype(np.float32) / 255.0

    if len(arr.shape) == 2:
        arr = arr[:, :, np.newaxis]

    return torch.from_numpy(arr).unsqueeze(0)
