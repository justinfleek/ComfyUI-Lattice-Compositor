(() => {
  const b = {
    sub: [20, 60],
    bass: [60, 250],
    lowMid: [250, 500],
    mid: [500, 2e3],
    highMid: [2e3, 4e3],
    high: [4e3, 2e4],
  };
  let g = !1;
  function M(t, c, l) {
    self.postMessage({
      type: "progress",
      payload: { phase: t, progress: c, message: l },
    });
  }
  function A(t) {
    self.postMessage({ type: "complete", payload: t });
  }
  function S(t) {
    self.postMessage({ type: "error", payload: { message: t } });
  }
  function T(t, c) {
    const l = t.length;
    for (let n = 0, s = 0; n < l; n++) {
      n < s && (([t[n], t[s]] = [t[s], t[n]]), ([c[n], c[s]] = [c[s], c[n]]));
      let a = l >> 1;
      for (; a >= 1 && s >= a; ) (s -= a), (a >>= 1);
      s += a;
    }
    for (let n = 2; n <= l; n *= 2) {
      const s = n / 2,
        a = l / n;
      for (let o = 0; o < l; o += n)
        for (let e = o, i = 0; e < o + s; e++, i += a) {
          const f = (-2 * Math.PI * i) / l,
            r = Math.cos(f),
            u = Math.sin(f),
            h = e + s,
            m = t[h] * r - c[h] * u,
            p = t[h] * u + c[h] * r;
          (t[h] = t[e] - m), (c[h] = c[e] - p), (t[e] += m), (c[e] += p);
        }
    }
  }
  function E(t, c) {
    const l = c,
      n = new Float32Array(l),
      s = new Float32Array(l);
    for (let e = 0; e < l; e++) {
      const i = 0.5 * (1 - Math.cos((2 * Math.PI * e) / (l - 1)));
      (n[e] = (t[e] || 0) * i), (s[e] = 0);
    }
    T(n, s);
    const a = l >> 1,
      o = new Float32Array(a);
    for (let e = 0; e < a; e++) o[e] = Math.sqrt(n[e] * n[e] + s[e] * s[e]) / l;
    return o;
  }
  function _(t, c, l) {
    const n = Math.floor(c / l),
      s = Math.ceil(t.length / n),
      a = [];
    for (let e = 0; e < s; e++) {
      if (g) return a;
      const i = e * n,
        f = Math.min(i + n, t.length);
      let r = 0;
      for (let u = i; u < f; u++) {
        const h = Math.abs(t[u]);
        h > r && (r = h);
      }
      a.push(r);
    }
    const o = Math.max(...a, 1e-4);
    return a.map((e) => e / o);
  }
  function C(t, c, l) {
    const n = Math.floor(c / l),
      s = Math.ceil(t.length / n),
      a = [];
    for (let e = 0; e < s; e++) {
      if (g) return a;
      const i = e * n,
        f = Math.min(i + n, t.length);
      let r = 0,
        u = 0;
      for (let m = i; m < f; m++) (r += t[m] * t[m]), u++;
      const h = u > 0 ? Math.sqrt(r / u) : 0;
      a.push(h);
    }
    const o = Math.max(...a, 1e-4);
    return a.map((e) => e / o);
  }
  function x(t, c, l) {
    const n = Math.floor(c / l),
      s = Math.ceil(t.length / n),
      a = c / 2048,
      o = { sub: [], bass: [], lowMid: [], mid: [], highMid: [], high: [] },
      e = {};
    for (const [i, [f, r]] of Object.entries(b))
      e[i] = { start: Math.floor(f / a), end: Math.ceil(r / a) };
    for (let i = 0; i < s; i++) {
      if (g) return o;
      i % 10 === 0 &&
        M(
          "frequency",
          i / s,
          `Analyzing frequency bands: ${Math.round((i / s) * 100)}%`,
        );
      const f = i * n;
      if (f + 2048 > t.length) {
        for (const u of Object.keys(o))
          o[u].push(o[u].length > 0 ? o[u][o[u].length - 1] : 0);
        continue;
      }
      const r = E(t.slice(f, f + 2048), 2048);
      for (const [u, { start: h, end: m }] of Object.entries(e)) {
        let p = 0,
          d = 0;
        for (let F = h; F < Math.min(m, r.length); F++) (p += r[F]), d++;
        o[u].push(d > 0 ? p / d : 0);
      }
    }
    for (const i of Object.keys(o)) {
      const f = Math.max(...o[i], 1e-4);
      o[i] = o[i].map((r) => r / f);
    }
    return o;
  }
  function I(t, c, l) {
    const n = Math.floor(c / l),
      s = Math.ceil(t.length / n),
      a = c / 2048,
      o = [];
    for (let i = 0; i < s; i++) {
      if (g) return o;
      i % 10 === 0 &&
        M(
          "spectral",
          i / s,
          `Computing spectral centroid: ${Math.round((i / s) * 100)}%`,
        );
      const f = i * n;
      if (f + 2048 > t.length) {
        o.push(o.length > 0 ? o[o.length - 1] : 0);
        continue;
      }
      const r = E(t.slice(f, f + 2048), 2048);
      let u = 0,
        h = 0;
      for (let p = 0; p < r.length; p++) {
        const d = p * a;
        (u += d * r[p]), (h += r[p]);
      }
      const m = h > 0 ? u / h : 0;
      o.push(m);
    }
    const e = Math.max(...o, 1e-4);
    return o.map((i) => i / e);
  }
  function L(t, c, l, n = 0.5) {
    const s = Math.floor(c / l),
      a = Math.ceil(t.length / s),
      o = [];
    let e = null;
    for (let r = 0; r < a; r++) {
      if (g) return [];
      r % 10 === 0 &&
        M("onsets", r / a, `Detecting onsets: ${Math.round((r / a) * 100)}%`);
      const u = r * s;
      if (u + 2048 > t.length) {
        o.push(0);
        continue;
      }
      const h = E(t.slice(u, u + 2048), 2048);
      if (e) {
        let m = 0;
        for (let p = 0; p < h.length; p++) {
          const d = h[p] - e[p];
          d > 0 && (m += d);
        }
        o.push(m);
      } else o.push(0);
      e = h;
    }
    const i = [],
      f = q(o, n);
    for (let r = 1; r < o.length - 1; r++)
      o[r] > o[r - 1] && o[r] > o[r + 1] && o[r] > f[r] && i.push(r);
    return i;
  }
  function q(t, c) {
    const n = [];
    for (let s = 0; s < t.length; s++) {
      const a = Math.max(0, s - 10),
        o = Math.min(t.length, s + 10 + 1),
        e = t.slice(a, o),
        i = e.reduce((r, u) => r + u, 0) / e.length,
        f = Math.sqrt(e.reduce((r, u) => r + (u - i) ** 2, 0) / e.length);
      n.push(i + (1 - c) * 2 * f);
    }
    return n;
  }
  function P(t, c) {
    M("bpm", 0, "Detecting BPM...");
    const l = 4,
      n = [];
    for (let d = 0; d < t.length; d += l) n.push(Math.abs(t[d]));
    const s = U(n, 0.1),
      a = 60,
      o = 200,
      e = c / l,
      i = Math.floor((60 / o) * e),
      f = Math.floor((60 / a) * e);
    let r = 0,
      u = i;
    const h = Math.min(s.length, e * 10),
      m = s.slice(0, h);
    for (let d = i; d <= f; d++) {
      if (g) return 120;
      let F = 0,
        w = 0;
      for (let y = 0; y < m.length - d; y++) (F += m[y] * m[y + d]), w++;
      w > 0 && ((F /= w), F > r && ((r = F), (u = d)));
    }
    const p = (60 * e) / u;
    return (
      M("bpm", 1, "BPM detection complete"),
      Math.round(Math.max(a, Math.min(o, p)))
    );
  }
  function U(t, c) {
    const l = [];
    let n = 0;
    for (const s of t) s > n ? (n = s) : (n = n * (1 - c) + s * c), l.push(n);
    return l;
  }
  async function Z(t, c, l) {
    g = !1;
    const n = t.length / c,
      s = Math.ceil(n * l);
    M("amplitude", 0, "Extracting amplitude envelope...");
    const a = _(t, c, l);
    if (g) throw new Error("Cancelled");
    M("amplitude", 1, "Amplitude envelope complete"),
      M("rms", 0, "Calculating RMS energy...");
    const o = C(t, c, l);
    if (g) throw new Error("Cancelled");
    M("rms", 1, "RMS energy complete"),
      M("frequency", 0, "Analyzing frequency bands...");
    const e = x(t, c, l);
    if (g) throw new Error("Cancelled");
    M("frequency", 1, "Frequency bands complete"),
      M("spectral", 0, "Computing spectral centroid...");
    const i = I(t, c, l);
    if (g) throw new Error("Cancelled");
    M("spectral", 1, "Spectral centroid complete"),
      M("onsets", 0, "Detecting onsets...");
    const f = L(t, c, l);
    if (g) throw new Error("Cancelled");
    M("onsets", 1, "Onset detection complete"), M("bpm", 0, "Detecting BPM...");
    const r = P(t, c);
    if (g) throw new Error("Cancelled");
    return (
      M("bpm", 1, "BPM detection complete"),
      {
        sampleRate: c,
        duration: n,
        frameCount: s,
        amplitudeEnvelope: a,
        rmsEnergy: o,
        spectralCentroid: i,
        frequencyBands: e,
        onsets: f,
        bpm: r,
      }
    );
  }
  self.onmessage = async (t) => {
    const c = t.data;
    switch (c.type) {
      case "analyze":
        try {
          const { channelData: l, sampleRate: n, fps: s } = c.payload,
            a = await Z(l, n, s);
          A(a);
        } catch (l) {
          l.message === "Cancelled"
            ? S("Analysis cancelled")
            : S(`Analysis failed: ${l.message}`);
        }
        break;
      case "cancel":
        g = !0;
        break;
    }
  };
})();
