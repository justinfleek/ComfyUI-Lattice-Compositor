export interface HSL {
  h: number;  // 0-360
  s: number;  // 0-1
  l: number;  // 0-1
}

export interface BaseColor {
  hue: number;
  saturation: number;
  lightness: number;
}

export interface HeroColor {
  hue: number;
  saturation: number;
  lightness: number;
}

export type MonitorType = "OLED" | "LCD";

export interface ThemeConfig {
  baseColor: BaseColor;
  heroColor: HeroColor;
  monitorType: MonitorType;
  blackBalance: number;  // 0-1
  mode: "dark" | "light";
}

export interface ThemeVariant {
  name: string;
  backgroundLightness: number;
  colors: {
    base00: string;
    base01: string;
    base02: string;
    base03: string;
    base04: string;
    base05: string;
    base06: string;
    base07: string;
    base08: string;
    base09: string;
    base0A: string;
    base0B: string;
    base0C: string;
    base0D: string;
    base0E: string;
    base0F: string;
  };
}
