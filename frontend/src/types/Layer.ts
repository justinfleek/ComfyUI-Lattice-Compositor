export interface Layer {
  id: string;
  name: string;
  type: 'spline' | 'text' | 'particles';
  visible: boolean;
  locked: boolean;
}
