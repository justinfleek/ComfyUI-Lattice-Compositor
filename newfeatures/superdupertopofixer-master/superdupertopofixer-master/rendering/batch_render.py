import subprocess
import tqdm
import argparse

import render_mitsuba


def render_batch(args, min_frame, max_frame):
    command = [
        "python",
        "render_mitsuba.py",
        args.scene_type,
        args.input_dir,
        args.output_dir,
        f"--min_frame={min_frame}",
        f"--max_frame={max_frame}",
    ]
    if args.skip_rendered:
        command.append("--skip_rendered")
    result = subprocess.run(
        command,
        capture_output=True,
        encoding="UTF-8",
    )
    if result.returncode != 0:
        print(f"Failed converting from {min_frame} to {max_frame} frames.")
        print(result.stderr)
        print(result.stdout)


def main():
    parser = argparse.ArgumentParser(
        prog="batch_render.py", description="Splits rendering into chucks"
    )
    parser.add_argument("batch_size", type=int)
    render_mitsuba.add_args(parser)
    args = parser.parse_args()

    # Compute batches
    renderer = render_mitsuba.Renderer()
    total_frame_nums = [
        renderer.get_frame_num(frame)
        for frame in renderer.get_numbered_frames(args.input_dir)
    ]
    min_frame = min(total_frame_nums)
    max_frame = max(total_frame_nums)
    if args.min_frame is not None:
        min_frame = max(min_frame, args.min_frame)
    if args.max_frame is not None:
        max_frame = min(max_frame, args.max_frame)
    for i in tqdm.tqdm(range(min_frame, max_frame, args.batch_size)):
        render_batch(args, i, i + args.batch_size)


if __name__ == "__main__":
    main()
