export class ColorWheel {
  private canvas: HTMLCanvasElement;
  private ctx: CanvasRenderingContext2D;
  private size: number;
  private centerX: number;
  private centerY: number;
  private radius: number;
  private onColorChange: (hsl: { h: number; s: number; l: number }) => void;
  private currentHSL: { h: number; s: number; l: number } = { h: 211, s: 1.0, l: 0.5 };

  constructor(
    container: HTMLElement,
    size: number,
    onColorChange: (hsl: { h: number; s: number; l: number }) => void
  ) {
    this.size = size;
    this.onColorChange = onColorChange;
    this.centerX = size / 2;
    this.centerY = size / 2;
    this.radius = size / 2 - 20;

    this.canvas = document.createElement("canvas");
    this.canvas.width = size;
    this.canvas.height = size;
    this.canvas.style.cursor = "crosshair";
    container.appendChild(this.canvas);

    const ctx = this.canvas.getContext("2d");
    if (!ctx) {
      throw new Error("Could not get 2D context");
    }
    this.ctx = ctx;

    this.draw();
    this.setupEventListeners();
  }

  private draw() {
    const { ctx, size, centerX, centerY, radius } = this;

    // Clear canvas
    ctx.clearRect(0, 0, size, size);

    // Draw color wheel (hue circle)
    const imageData = ctx.createImageData(size, size);
    const data = imageData.data;

    for (let y = 0; y < size; y++) {
      for (let x = 0; x < size; x++) {
        const dx = x - centerX;
        const dy = y - centerY;
        const distance = Math.sqrt(dx * dx + dy * dy);
        const angle = Math.atan2(dy, dx);

        if (distance <= radius) {
          const hue = ((angle * 180) / Math.PI + 180) % 360;
          const saturation = Math.min(1, distance / radius);
          const lightness = this.currentHSL.l;

          const rgb = this.hslToRgb(hue, saturation, lightness);
          const index = (y * size + x) * 4;
          data[index] = rgb.r;
          data[index + 1] = rgb.g;
          data[index + 2] = rgb.b;
          data[index + 3] = 255;
        }
      }
    }

    ctx.putImageData(imageData, 0, 0);

    // Draw lightness slider on the right
    const sliderWidth = 30;
    const sliderX = size - sliderWidth - 10;
    const sliderHeight = radius * 2;
    const sliderY = centerY - radius;

    const gradient = ctx.createLinearGradient(
      sliderX,
      sliderY,
      sliderX,
      sliderY + sliderHeight
    );
    gradient.addColorStop(0, `hsl(${this.currentHSL.h}, 100%, 100%)`);
    gradient.addColorStop(0.5, `hsl(${this.currentHSL.h}, 100%, 50%)`);
    gradient.addColorStop(1, `hsl(${this.currentHSL.h}, 100%, 0%)`);

    ctx.fillStyle = gradient;
    ctx.fillRect(sliderX, sliderY, sliderWidth, sliderHeight);

    // Draw lightness indicator
    const lightnessY = sliderY + sliderHeight * (1 - this.currentHSL.l);
    ctx.strokeStyle = "#fff";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.moveTo(sliderX - 5, lightnessY);
    ctx.lineTo(sliderX + sliderWidth + 5, lightnessY);
    ctx.stroke();

    // Draw saturation/lightness indicator
    const satX = centerX + Math.cos((this.currentHSL.h * Math.PI) / 180) * this.currentHSL.s * radius;
    const satY = centerY + Math.sin((this.currentHSL.h * Math.PI) / 180) * this.currentHSL.s * radius;

    ctx.strokeStyle = "#fff";
    ctx.lineWidth = 3;
    ctx.beginPath();
    ctx.arc(satX, satY, 8, 0, Math.PI * 2);
    ctx.stroke();
    ctx.strokeStyle = "#000";
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.arc(satX, satY, 8, 0, Math.PI * 2);
    ctx.stroke();
  }

  private hslToRgb(h: number, s: number, l: number): { r: number; g: number; b: number } {
    h = h % 360;
    const c = (1 - Math.abs(2 * l - 1)) * s;
    const x = c * (1 - Math.abs(((h / 60) % 2) - 1));
    const m = l - c / 2;

    let r = 0;
    let g = 0;
    let b = 0;

    if (h < 60) {
      r = c;
      g = x;
      b = 0;
    } else if (h < 120) {
      r = x;
      g = c;
      b = 0;
    } else if (h < 180) {
      r = 0;
      g = c;
      b = x;
    } else if (h < 240) {
      r = 0;
      g = x;
      b = c;
    } else if (h < 300) {
      r = x;
      g = 0;
      b = c;
    } else {
      r = c;
      g = 0;
      b = x;
    }

    return {
      r: Math.round((r + m) * 255),
      g: Math.round((g + m) * 255),
      b: Math.round((b + m) * 255)
    };
  }

  private setupEventListeners() {
    this.canvas.addEventListener("click", (e) => {
      const rect = this.canvas.getBoundingClientRect();
      const x = e.clientX - rect.left;
      const y = e.clientY - rect.top;

      const dx = x - this.centerX;
      const dy = y - this.centerY;
      const distance = Math.sqrt(dx * dx + dy * dy);
      const angle = Math.atan2(dy, dx);

      const sliderWidth = 30;
      const sliderX = this.size - sliderWidth - 10;
      const sliderHeight = this.radius * 2;
      const sliderY = this.centerY - this.radius;

      // Check if clicking on lightness slider
      if (x >= sliderX && x <= sliderX + sliderWidth && y >= sliderY && y <= sliderY + sliderHeight) {
        const lightness = 1 - (y - sliderY) / sliderHeight;
        this.currentHSL.l = Math.max(0, Math.min(1, lightness));
      } else if (distance <= this.radius) {
        // Clicking on color wheel
        const hue = ((angle * 180) / Math.PI + 180) % 360;
        const saturation = Math.min(1, distance / this.radius);
        this.currentHSL.h = hue;
        this.currentHSL.s = saturation;
      }

      this.draw();
      this.onColorChange({ ...this.currentHSL });
    });

    this.canvas.addEventListener("mousemove", (e) => {
      if (e.buttons === 1) {
        // Mouse is being dragged
        const rect = this.canvas.getBoundingClientRect();
        const x = e.clientX - rect.left;
        const y = e.clientY - rect.top;

        const dx = x - this.centerX;
        const dy = y - this.centerY;
        const distance = Math.sqrt(dx * dx + dy * dy);
        const angle = Math.atan2(dy, dx);

        const sliderWidth = 30;
        const sliderX = this.size - sliderWidth - 10;
        const sliderHeight = this.radius * 2;
        const sliderY = this.centerY - this.radius;

        if (x >= sliderX && x <= sliderX + sliderWidth && y >= sliderY && y <= sliderY + sliderHeight) {
          const lightness = 1 - (y - sliderY) / sliderHeight;
          this.currentHSL.l = Math.max(0, Math.min(1, lightness));
        } else if (distance <= this.radius) {
          const hue = ((angle * 180) / Math.PI + 180) % 360;
          const saturation = Math.min(1, distance / this.radius);
          this.currentHSL.h = hue;
          this.currentHSL.s = saturation;
        }

        this.draw();
        this.onColorChange({ ...this.currentHSL });
      }
    });
  }

  public setHSL(hsl: { h: number; s: number; l: number }) {
    this.currentHSL = { ...hsl };
    this.draw();
  }

  public getHSL(): { h: number; s: number; l: number } {
    return { ...this.currentHSL };
  }
}
