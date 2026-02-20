import type { JSX } from "preact";
import { useState } from "preact/hooks";

interface CompositorState {
  connected: boolean;
  activeNodes: number;
}

export function App(): JSX.Element {
  const [state, setState] = useState<CompositorState>({
    connected: false,
    activeNodes: 0,
  });

  const handleConnect = (): void => {
    setState((prev) => ({ ...prev, connected: !prev.connected }));
  };

  return (
    <div class="compositor">
      <header class="header">
        <h1>Lattice Compositor</h1>
        <span
          class={`status ${state.connected ? "connected" : "disconnected"}`}
        >
          {state.connected ? "Connected" : "Disconnected"}
        </span>
      </header>

      <main class="main">
        <section class="panel">
          <h2>Control Panel</h2>
          <button type="button" onClick={handleConnect} class="btn">
            {state.connected ? "Disconnect" : "Connect"}
          </button>
          <p>Active Nodes: {state.activeNodes}</p>
        </section>

        <section class="canvas">
          <div class="placeholder">Node Graph Canvas</div>
        </section>
      </main>

      <footer class="footer">
        <p>Lattice Compositor v0.1.0</p>
      </footer>
    </div>
  );
}
