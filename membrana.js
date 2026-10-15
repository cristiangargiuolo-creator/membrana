/* membrana
 *
 * Il film arriva come flusso VP8 grezzo (assets/film.ivf, 480x270, 15 fps, un fotogramma chiave per battuta,
 * error-resilient, 8 partizioni DCT). Due decoder WebCodecs lo leggono in parallelo:
 *   A riceve i dati giusti e non si vede;
 *   B riceve i dati sbagliati (chiavi tolte, fotogrammi ripetuti, byte riscritti) e si vede in grigio.
 * Dove B e A non coincidono riaffiora il colore di A (come codecmat.py --color-errors).
 * La stessa mappa del danno rompe il suono (come codec_audio.py).
 * Niente spiegazioni in pagina: chi cerca trova (sorgente, console, selezione, tastiera).
 */
'use strict';
(() => {
  const W = 480, H = 270, FPS = 15, LOOK = 5;
  const MB_COLS = 30, MB_ROWS = 17, NPART = 8;
  const GEL = [200, 240, 60];
  const $ = s => document.querySelector(s);
  const ui = {
    schermo: $('#schermo'), canvas: $('#film'), dump: $('#dump'), fuga: $('#fuga'), stato: $('#stato'),
    partitura: $('#partitura'), entra: $('#entra'), cursore: $('#cursore'), palco: $('#palco'),
    palcoIn: $('#palco-in'), disegno: $('#disegno'), icona: $('#icona'),
  };

  let S = null, film = null, frames = null, keyIdx = [], CFG = null;
  let running = false, lastF = -1, DUR = 0, curF = 0;
  let esploso = false;

  const stat = { decoded: 0, keysLost: 0, bytes: 0, crashes: 0, skipped: 0, colorFrames: 0, shown: 0 };
  const barErr = [];          // fotogrammi con colore per battuta, in questa visita
  const flips = [];           // byte riscritti di recente: {row, x, at, t}

  // ------------------------------------------------------------------ flusso IVF
  function parseIVF(buf) {
    const dv = new DataView(buf), u8 = new Uint8Array(buf);
    let p = dv.getUint16(6, true);
    const out = [];
    while (p + 12 <= buf.byteLength) {
      const size = dv.getUint32(p, true);
      const data = u8.subarray(p + 12, p + 12 + size);
      const tag = data[0] | (data[1] << 8) | (data[2] << 16);
      const key = (tag & 1) === 0, firstPart = (tag >> 5) & 0x7ffff;
      out.push({ data, off: p + 12, key, firstPart, parts: key ? null : partitions(data, 3 + firstPart) });
      p += 12 + size;
    }
    return out;
  }
  // 8 partizioni DCT: la riga di macroblocchi r sta nella partizione r % 8
  function partitions(d, p1) {
    let off = p1 + 3 * (NPART - 1);
    const parts = [];
    for (let k = 0; k < NPART; k++) {
      const size = k < NPART - 1 ? d[p1 + 3 * k] | (d[p1 + 3 * k + 1] << 8) | (d[p1 + 3 * k + 2] << 16) : d.length - off;
      if (size < 0 || off + size > d.length) return null;
      parts.push([off, size]);
      off += size;
    }
    return parts;
  }
  const keyBefore = i => { let k = 0; for (const x of keyIdx) { if (x <= i) k = x; else break; } return k; };
  const barOf = t => Math.min(S.nbars - 1, Math.max(0, Math.floor(t / S.bar + 1e-6)));

  // ------------------------------------------------------------------ decoder
  class Dec {
    constructor(name) { this.name = name; this.q = []; this.map = new Map(); this.seq = 0; this.next = 0; this.make(); }
    make() {
      if (this.d && this.d.state !== 'closed') { try { this.d.close(); } catch (e) { /* già chiuso */ } }
      this.map.clear();
      this.needKey = true;
      this.broken = false;
      this.d = new VideoDecoder({
        output: f => {
          const idx = this.map.get(f.timestamp);
          this.map.delete(f.timestamp);
          if (idx === undefined) { f.close(); return; }
          this.q.push({ f, idx });
          if (this.name === 'B') stat.decoded++;
        },
        error: () => { this.broken = true; },
      });
      this.d.configure(CFG);
    }
    feed(data, key, idx) {
      if (this.d.state !== 'configured' || (this.needKey && !key)) return false;
      const ts = (this.seq++) * 1000;
      this.map.set(ts, idx);
      try {
        this.d.decode(new EncodedVideoChunk({ type: key ? 'key' : 'delta', timestamp: ts, data }));
      } catch (e) {
        this.map.delete(ts);
        this.broken = true;
        return false;
      }
      if (key) this.needKey = false;
      return true;
    }
    busy() { return this.d.state !== 'configured' || this.d.decodeQueueSize > 6; }
    pick(f) {
      while (this.q.length > 1 && this.q[1].idx <= f) this.q.shift().f.close();
      return this.q.length && this.q[0].idx <= f ? this.q[0] : null;
    }
    dropAll() { for (const x of this.q) x.f.close(); this.q.length = 0; }
    rebase(f) {
      while (this.q.length > 1) this.q.shift().f.close();
      if (this.q.length) this.q[0].idx = f;
      for (const k of this.map.keys()) this.map.set(k, f);
    }
  }
  let A = null, B = null;

  // ------------------------------------------------------------------ cosa riceve B
  const mosh = {
    hold: false, holdSrc: -1, drag: 0, pos: null, bloomSrc: -1, bloomUntil: -1, freezing: false,
    forget: false, amnesia: false, recall: null,
  };
  let lastData = null, lastFlipAt = [];

  function biggestRecentDelta(i) {
    let best = -1, size = -1;
    for (let k = Math.max(0, i - 8); k <= i; k++) {
      if (!frames[k].key && frames[k].data.length > size) { size = frames[k].data.length; best = k; }
    }
    return best < 0 ? i : best;
  }

  function corrupt(src, fr, pos, n) {
    const d = new Uint8Array(src);
    const at = [];
    if (!fr.parts) return { d, at };
    const now = performance.now();
    for (let k = 0; k < n; k++) {
      let row, x;
      if (pos) {
        row = Math.floor((pos.y + (Math.random() - 0.5) * 0.05) * MB_ROWS);
        x = Math.min(0.999, Math.max(0, pos.x + (Math.random() - 0.5) * 0.04));
      } else {
        row = (Math.random() * MB_ROWS) | 0;
        x = Math.random();
      }
      row = Math.min(MB_ROWS - 1, Math.max(0, row));
      const p = row % NPART, rowsIn = Math.ceil((MB_ROWS - p) / NPART), j = Math.floor(row / NPART);
      const [off, size] = fr.parts[p];
      if (size < 4) continue;
      const a = off + Math.min(size - 1, Math.floor(((j + x) / rowsIn) * size));
      const bit = 1 << ((Math.random() * 8) | 0);
      d[a] ^= bit;
      at.push(a);
      if (k < 6) flips.push({ row, x, at: a, bit, t: now });
    }
    if (!pos && n > 8 && fr.firstPart > 32 && Math.random() < 0.15) {
      const a = 3 + Math.floor(fr.firstPart * (0.4 + 0.6 * Math.random()));
      d[a] ^= 1 << ((Math.random() * 8) | 0);
      at.push(a);
    }
    while (flips.length > 40) flips.shift();
    return { d, at };
  }

  function stepB(i) {
    const fr = frames[i], t = i / FPS, bar = barOf(t), prot = t >= S.protect;
    if (mosh.recall != null && !prot) {
      B.feed(frames[mosh.recall].data, true, i);
      if (mosh.recall !== keyBefore(i)) sound.colata(t);
      mosh.recall = null;
      if (fr.key) return;
    }
    if (B.needKey) {
      // dopo un crollo il decoder riparte da una battuta già passata: un ricordo
      const cur = keyBefore(i);
      const pool = keyIdx.filter(k => k <= cur && k >= cur - 6 * S.bar * FPS);   // ricordi recenti
      const k = prot || B.fresh ? cur : pool[(Math.random() * pool.length) | 0];
      B.fresh = false;
      B.feed(frames[k].data, true, i);
      if (k !== cur) sound.colata(t);
      if (fr.key) return;
    }
    if (fr.key) {
      const lose = !prot && (mosh.hold || mosh.forget || mosh.amnesia || S.dropSet.has(bar));
      if (lose) {
        mosh.forget = false;
        stat.keysLost++;
        sound.colata(t);
        lastData = fr.data; lastFlipAt = [];
        return;
      }
      B.feed(fr.data, true, i);
      lastData = fr.data; lastFlipAt = [];
      return;
    }
    let src = i;
    if (!prot) {
      if (mosh.hold) {
        if (mosh.holdSrc < 0) mosh.holdSrc = biggestRecentDelta(i);
        src = mosh.holdSrc;
      } else {
        const L = S.bloomAt.get(i);
        if (L) { mosh.bloomSrc = biggestRecentDelta(i); mosh.bloomUntil = i + L; }
        if (i < mosh.bloomUntil) src = mosh.bloomSrc;
      }
    }
    if (src !== i && !mosh.freezing) { mosh.freezing = true; sound.freeze(t, true); }
    if (src === i && mosh.freezing) { mosh.freezing = false; sound.freeze(t, false); }

    let data = frames[src].data, n = 0, pos = null, at = [];
    if (!prot) {
      if (S.corruptSet.has(i)) n += 4 + (S.q[bar] >> 2);
      if (mosh.drag >= 1) {
        const k = Math.min(24, Math.round(mosh.drag));
        n += k;
        mosh.drag = Math.max(0, mosh.drag - k);
        pos = mosh.pos;
      }
    }
    if (n > 0) {
      const c = corrupt(data, frames[src], pos, n);
      data = c.d; at = c.at;
      stat.bytes += at.length;
      sound.bytes(data, pos);
      titolo.ferisci(data, at);
      if (pos) cursore.mostra(at[0], data[at[0]]);
    }
    lastData = data; lastFlipAt = at;
    B.feed(data, false, i);
  }

  function feedA(f) {
    if (A.broken) { A.make(); A.dropAll(); A.next = keyBefore(Math.max(0, f)); }
    if (A.next < f - 40) { A.make(); A.dropAll(); A.next = keyBefore(f); }
    while (A.next <= f + LOOK && A.next < frames.length && !A.busy()) {
      const i = A.next, fr = frames[i];
      if (A.needKey && !fr.key) { A.next = keyBefore(i); continue; }
      A.feed(fr.data, fr.key, i);
      A.next++;
    }
  }

  function feedB(f) {
    if (B.broken) { stat.crashes++; B.make(); sound.crash(); }
    if (B.next < f - 12) {
      // la macchina è rimasta indietro: anche i fotogrammi saltati sono un errore (tranne nel finale)
      if (f / FPS >= S.protect) B.next = Math.max(keyBefore(f), B.next);
      else { stat.skipped += f - B.next; B.next = f; }
    }
    while (B.next <= f + LOOK && B.next < frames.length && !B.busy()) stepB(B.next++);
  }

  // ------------------------------------------------------------------ immagine (WebGL2)
  const gfx = {
    init(canvas) {
      const gl = canvas.getContext('webgl2', { preserveDrawingBuffer: true, antialias: false, depth: false, premultipliedAlpha: false });
      if (!gl) return false;
      this.gl = gl;
      const vs = `#version 300 es
        out vec2 uv;
        void main() { vec2 p = vec2(float((gl_VertexID << 1) & 2), float(gl_VertexID & 2)); uv = p; gl_Position = vec4(p * 2.0 - 1.0, 0.0, 1.0); }`;
      const head = `#version 300 es
        precision highp float;
        in vec2 uv; out vec4 o;
        float lum(vec3 c) { return dot(c, vec3(0.299, 0.587, 0.114)); }
        vec2 vid(vec2 u) { return vec2(u.x, 1.0 - u.y); }
      `;
      const prog = fs => {
        const p = gl.createProgram();
        for (const [type, src] of [[gl.VERTEX_SHADER, vs], [gl.FRAGMENT_SHADER, head + fs]]) {
          const s = gl.createShader(type);
          gl.shaderSource(s, src);
          gl.compileShader(s);
          if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw new Error(gl.getShaderInfoLog(s));
          gl.attachShader(p, s);
        }
        gl.linkProgram(p);
        if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error(gl.getProgramInfoLog(p));
        const u = {};
        const n = gl.getProgramParameter(p, gl.ACTIVE_UNIFORMS);
        for (let k = 0; k < n; k++) { const name = gl.getActiveUniform(p, k).name; u[name] = gl.getUniformLocation(p, name); }
        return { p, u };
      };
      this.pDiff = prog(`uniform sampler2D A, B;
        void main() { o = vec4(abs(lum(texture(B, vid(uv)).rgb) - lum(texture(A, vid(uv)).rgb)), 0.0, 0.0, 1.0); }`);
      this.pBlur = prog(`uniform sampler2D T; uniform vec2 d;
        void main() {
          float w[5] = float[5](0.1716, 0.1584, 0.1246, 0.0835, 0.0477);
          float s = texture(T, uv).r * w[0];
          for (int k = 1; k < 5; k++) s += (texture(T, uv + d * float(k)).r + texture(T, uv - d * float(k)).r) * w[k];
          o = vec4(s, 0.0, 0.0, 1.0);
        }`);
      this.pAlpha = prog(`uniform sampler2D D, P; uniform float g, prot;
        void main() {
          float d = texture(D, uv).r;
          float a = pow(clamp((d - 0.012 / g) / (0.07 / g), 0.0, 1.0), 0.7);
          float p = texture(P, uv).r;
          a = mix(max(a, p * 0.77), p * 0.72, prot);
          o = vec4(a, 0.0, 0.0, 1.0);
        }`);
      this.pComp = prog(`uniform sampler2D A, B, AL; uniform float k;
        void main() {
          vec3 cb = texture(B, vid(uv)).rgb, ca = texture(A, vid(uv)).rgb;
          float a = texture(AL, uv).r;
          o = vec4(clamp(vec3(lum(cb)) + a * (ca - vec3(lum(ca))) * k, 0.0, 1.0), 1.0);
        }`);
      this.pStats = prog(`uniform sampler2D A, AL;
        void main() {
          vec2 cell = floor(gl_FragCoord.xy);
          vec3 s = vec3(0.0); float sa = 0.0;
          for (int j = 0; j < 6; j++) for (int i = 0; i < 6; i++) {
            vec2 u = (cell + (vec2(float(i), float(j)) + 0.5) / 6.0) / vec2(16.0, 9.0);
            float a = texture(AL, u).r;
            s += a * texture(A, vid(u)).rgb; sa += a;
          }
          o = vec4(s / 36.0, sa / 36.0);
        }`);
      // strati dell'esploso
      this.pEdge = prog(`uniform sampler2D A; uniform vec2 px;
        float L(vec2 q) { return lum(texture(A, vid(uv + q * px)).rgb); }
        void main() {
          float gx = -L(vec2(-1,-1)) - 2.0*L(vec2(-1,0)) - L(vec2(-1,1)) + L(vec2(1,-1)) + 2.0*L(vec2(1,0)) + L(vec2(1,1));
          float gy = -L(vec2(-1,-1)) - 2.0*L(vec2(0,-1)) - L(vec2(1,-1)) + L(vec2(-1,1)) + 2.0*L(vec2(0,1)) + L(vec2(1,1));
          o = vec4(0.0, 0.0, 0.0, smoothstep(0.16, 0.45, length(vec2(gx, gy))));
        }`);
      this.pGray = prog(`uniform sampler2D B;
        void main() { o = vec4(vec3(lum(texture(B, vid(uv)).rgb)), 1.0); }`);
      this.pDmg = prog(`uniform sampler2D AL;
        void main() {
          float a = texture(AL, uv).r;
          vec3 c = mix(vec3(0.784, 0.941, 0.235), vec3(0.0), smoothstep(0.78, 0.97, a));
          o = vec4(c, smoothstep(0.02, 0.45, a));
        }`);
      const tex = (w, h) => {
        const t = gl.createTexture();
        gl.bindTexture(gl.TEXTURE_2D, t);
        gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA8, w, h, 0, gl.RGBA, gl.UNSIGNED_BYTE, null);
        this.params();
        return t;
      };
      const target = (w, h) => {
        const t = tex(w, h), fb = gl.createFramebuffer();
        gl.bindFramebuffer(gl.FRAMEBUFFER, fb);
        gl.framebufferTexture2D(gl.FRAMEBUFFER, gl.COLOR_ATTACHMENT0, gl.TEXTURE_2D, t, 0);
        return { t, fb, w, h };
      };
      this.tA = tex(W, H); this.tB = tex(W, H);
      this.rDiff = target(W, H); this.rBlur = target(W, H); this.rBlur2 = target(W, H);
      this.rAl = [target(W, H), target(W, H)]; this.cur = 0;
      this.rStats = target(16, 9);
      this.px = new Uint8Array(16 * 9 * 4);
      this.clear();
      return true;
    },
    params() {
      const gl = this.gl;
      for (const [k, v] of [[gl.TEXTURE_MIN_FILTER, gl.NEAREST], [gl.TEXTURE_MAG_FILTER, gl.NEAREST],
        [gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE], [gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE]]) gl.texParameteri(gl.TEXTURE_2D, k, v);
    },
    clear() {
      const gl = this.gl;
      for (const r of this.rAl) { gl.bindFramebuffer(gl.FRAMEBUFFER, r.fb); gl.clearColor(0, 0, 0, 1); gl.clear(gl.COLOR_BUFFER_BIT); }
    },
    upload(tex, frame) {
      const gl = this.gl;
      gl.bindTexture(gl.TEXTURE_2D, tex);
      gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, gl.RGBA, gl.UNSIGNED_BYTE, frame);
      this.params();
    },
    pass(pr, out, texs, set) {
      const gl = this.gl;
      gl.useProgram(pr.p);
      texs.forEach(([name, t], k) => { gl.activeTexture(gl.TEXTURE0 + k); gl.bindTexture(gl.TEXTURE_2D, t); gl.uniform1i(pr.u[name], k); });
      if (set) set(pr.u);
      gl.bindFramebuffer(gl.FRAMEBUFFER, out ? out.fb : null);
      gl.viewport(0, 0, out ? out.w : W, out ? out.h : H);
      gl.drawArrays(gl.TRIANGLES, 0, 3);
    },
    copy(ctx, clear) {
      if (clear) ctx.clearRect(0, 0, W, H);
      ctx.drawImage(this.gl.canvas, 0, 0);
    },
    run(prot, layers) {
      const gl = this.gl;
      const prev = this.rAl[this.cur], next = this.rAl[1 - this.cur];
      this.pass(this.pDiff, this.rDiff, [['A', this.tA], ['B', this.tB]]);
      this.pass(this.pBlur, this.rBlur, [['T', this.rDiff.t]], u => gl.uniform2f(u.d, 1 / W, 0));
      this.pass(this.pBlur, this.rBlur2, [['T', this.rBlur.t]], u => gl.uniform2f(u.d, 0, 1 / H));
      this.pass(this.pAlpha, next, [['D', this.rBlur2.t], ['P', prev.t]], u => { gl.uniform1f(u.g, 2.0); gl.uniform1f(u.prot, prot ? 1 : 0); });
      this.cur = 1 - this.cur;
      if (layers) {
        this.pass(this.pEdge, null, [['A', this.tA]], u => gl.uniform2f(u.px, 1 / W, 1 / H));
        this.copy(layers.a, true);
        this.pass(this.pGray, null, [['B', this.tB]]);
        this.copy(layers.b, false);
        this.pass(this.pDmg, null, [['AL', next.t]]);
        this.copy(layers.d, true);
      }
      this.pass(this.pComp, null, [['A', this.tA], ['B', this.tB], ['AL', next.t]], u => gl.uniform1f(u.k, 2.3));
      if (layers) this.copy(layers.m, false);
      this.pass(this.pStats, this.rStats, [['A', this.tA], ['AL', next.t]]);
      gl.bindFramebuffer(gl.FRAMEBUFFER, this.rStats.fb);
      gl.readPixels(0, 0, 16, 9, gl.RGBA, gl.UNSIGNED_BYTE, this.px);
      return this.px;
    },
  };

  // ------------------------------------------------------------------ suono (Web Audio)
  const EDGES = Array.from({ length: 10 }, (_, r) => 16000 * Math.pow(40 / 16000, r / 9));   // riga 0 = acuti
  const sound = {
    async init(arrayBuf) {
      const ctx = new (window.AudioContext || window.webkitAudioContext)();
      this.ctx = ctx;
      this.buf = await ctx.decodeAudioData(arrayBuf);
      this.input = ctx.createGain();
      const split = ctx.createChannelSplitter(2), merge = ctx.createChannelMerger(2);
      this.input.connect(split);
      this.bands = [[], []];
      for (let ch = 0; ch < 2; ch++) {
        let node = null;
        for (let r = 0; r < 9; r++) {
          const f = ctx.createBiquadFilter();
          f.type = 'peaking';
          f.frequency.value = Math.sqrt(EDGES[r] * EDGES[r + 1]);
          f.Q.value = f.frequency.value / (EDGES[r] - EDGES[r + 1]);
          f.gain.value = 0;
          if (node) node.connect(f); else split.connect(f, ch);
          node = f;
          this.bands[ch].push(f);
        }
        node.connect(merge, 0, ch);
      }
      this.dry = ctx.createGain();
      this.crush = ctx.createGain();
      this.crush.gain.value = 0;
      const shaper = ctx.createWaveShaper();
      const curve = new Float32Array(4096);
      for (let k = 0; k < curve.length; k++) curve[k] = Math.round((k / 2047.5 - 1) * 12) / 12;
      shaper.curve = curve;
      this.bus = ctx.createGain();
      this.bus.gain.value = 0.9;
      merge.connect(this.dry).connect(this.bus);
      merge.connect(shaper).connect(this.crush).connect(this.bus);
      const lim = ctx.createDynamicsCompressor();
      lim.threshold.value = -2; lim.knee.value = 0; lim.ratio.value = 20; lim.attack.value = 0.002; lim.release.value = 0.12;
      this.bus.connect(lim).connect(ctx.destination);
      this.playing = false;
      this.off = 0;
    },
    play(offset) {
      this.stop();
      const s = this.ctx.createBufferSource();
      s.buffer = this.buf;
      s.connect(this.input);
      s.start(0, offset);
      this.src = s;
      this.t0 = this.ctx.currentTime;
      this.off = offset;
      this.playing = true;
    },
    stop() {
      if (this.src) { try { this.src.stop(); } catch (e) { /* già fermo */ } this.src.disconnect(); this.src = null; }
      if (this.held) this.freeze(0, false);
      this.playing = false;
    },
    time() {
      if (!this.playing) return this.off;
      const lat = this.ctx.outputLatency || this.ctx.baseLatency || 0;
      return this.ctx.currentTime - this.t0 + this.off - lat;
    },
    damage(rows) {
      const now = this.ctx.currentTime;
      for (let ch = 0; ch < 2; ch++) {
        for (let r = 0; r < 9; r++) {
          const aR = Math.min(0.9, rows[ch][r] * 3.0);
          this.bands[ch][r].gain.setTargetAtTime(20 * Math.log10(1 - 0.75 * aR), now, 0.04);
        }
      }
    },
    grain(t, a, b, level, dur) {
      const ctx = this.ctx, now = ctx.currentTime;
      const s = ctx.createBufferSource(), g = ctx.createGain();
      s.buffer = this.buf;
      s.loop = true;
      s.loopStart = Math.max(0, t - a);
      s.loopEnd = Math.max(s.loopStart + 0.02, t - b);
      g.gain.setValueAtTime(0, now);
      g.gain.linearRampToValueAtTime(level, now + 0.02);
      s.connect(g).connect(this.input);
      s.start(now, s.loopStart);
      if (dur) { g.gain.setTargetAtTime(0, now + 0.15, dur / 4); s.stop(now + dur); }
      return { s, g };
    },
    colata(t) {
      if (!this.playing) return;
      this.grain(t, 0.32, 0.06, 0.55, 2.6);
      this.duck(0.6, 0.9);
    },
    freeze(t, on) {
      if (on && this.playing && !this.held) {
        this.held = this.grain(t, 0.1, 0.012, 0.6, 0);
        this.dry.gain.setTargetAtTime(0.5, this.ctx.currentTime, 0.05);
      } else if (!on && this.held) {
        const now = this.ctx.currentTime, h = this.held;
        h.g.gain.setTargetAtTime(0, now, 0.06);
        h.s.stop(now + 0.4);
        this.held = null;
        this.dry.gain.setTargetAtTime(1, now, 0.1);
      }
    },
    duck(to, rec) {
      const now = this.ctx.currentTime;
      this.dry.gain.cancelScheduledValues(now);
      this.dry.gain.setTargetAtTime(to, now, 0.02);
      this.dry.gain.setTargetAtTime(this.held ? 0.5 : 1, now + 0.1, rec / 3);
    },
    bytes(data, pos) {
      if (!this.playing) return;
      const ctx = this.ctx, sr = ctx.sampleRate, now = ctx.currentTime;
      const n = Math.round(0.133 * sr), L = data.length;
      const ab = ctx.createBuffer(1, n, sr), ch = ab.getChannelData(0);
      for (let k = 0; k < n; k++) {
        const x = (k / (n - 1)) * (L - 1), i0 = x | 0, fr = x - i0;
        const v = (data[i0] * (1 - fr) + data[Math.min(L - 1, i0 + 1)] * fr - 128) / 128;
        ch[k] = v * Math.exp(-k / (0.045 * sr));
      }
      const y = pos ? pos.y : Math.random(), x = pos ? pos.x : Math.random();
      const s = ctx.createBufferSource(), bp = ctx.createBiquadFilter(), pan = ctx.createStereoPanner(), g = ctx.createGain();
      s.buffer = ab;
      bp.type = 'bandpass';
      bp.frequency.value = Math.exp(Math.log(5500) + (Math.log(300) - Math.log(5500)) * y);
      bp.Q.value = 1.1;
      pan.pan.value = x * 2 - 1;
      g.gain.value = 0.5;
      s.connect(bp).connect(pan).connect(g).connect(this.bus);
      s.start(now);
      this.crush.gain.cancelScheduledValues(now);
      this.crush.gain.setValueAtTime(0.5, now);
      this.crush.gain.setTargetAtTime(0, now + 0.06, 0.05);
      this.duck(0.55, 0.2);
    },
    crash() {
      if (!this.playing) return;
      const now = this.ctx.currentTime;
      this.crush.gain.cancelScheduledValues(now);
      this.crush.gain.setValueAtTime(0.9, now);
      this.crush.gain.setTargetAtTime(0, now + 0.25, 0.12);
      this.duck(0.15, 0.6);
    },
  };

  // ------------------------------------------------------------------ il flusso come sfondo
  const hex = Array.from({ length: 256 }, (_, k) => k.toString(16).padStart(2, '0'));
  const dump = {
    cap: 4000,
    measure() {
      const cw = 6.6, lh = 12;          // Courier New 11px
      const cols = Math.floor((innerWidth - 6) / cw), rows = Math.ceil(innerHeight / lh);
      this.cap = Math.max(200, Math.floor((cols * rows) / 3));
    },
    // i byte del file a partire dal fotogramma corrente; quelli riscritti in lime, l'intestazione VP8 in nero
    draw(i, data, at) {
      const fr = frames[i];
      const u8 = film, start = fr.off, n = Math.min(this.cap, u8.length - start);
      const hit = new Set(at);
      let s = '';
      const len = data ? data.length : fr.data.length;
      for (let k = 0; k < n; k++) {
        const inFrame = k < len;
        const v = inFrame && data ? data[k] : u8[start + k];
        if (inFrame && hit.has(k)) s += `<b>${hex[v]}</b> `;
        else if (inFrame && k < 3) s += `<i>${hex[v]}</i> `;
        else s += hex[v] + ' ';
      }
      ui.dump.innerHTML = s;
    },
    text(str) { ui.dump.textContent = str; },
  };

  // ------------------------------------------------------------------ il colore cola fuori dalla membrana
  const fuga = {
    init() {
      this.ctx = ui.fuga.getContext('2d');
      this.parts = [];
      this.resize();
      // sprite: alone lime e nucleo nero ad aerografo, una volta sola
      const glow = document.createElement('canvas');
      glow.width = glow.height = 128;
      const g = glow.getContext('2d');
      const grd = g.createRadialGradient(64, 64, 0, 64, 64, 64);
      grd.addColorStop(0, 'rgba(200,240,60,0.95)');
      grd.addColorStop(0.45, 'rgba(200,240,60,0.75)');
      grd.addColorStop(1, 'rgba(200,240,60,0)');
      g.fillStyle = grd;
      g.fillRect(0, 0, 128, 128);
      this.glow = glow;
      const core = document.createElement('canvas');
      core.width = core.height = 64;
      const c = core.getContext('2d');
      let seed = 7;
      const rnd = () => ((seed = (seed * 16807) % 2147483647) / 2147483647);
      c.fillStyle = '#000';
      c.beginPath(); c.arc(32, 32, 9, 0, Math.PI * 2); c.fill();
      for (let k = 0; k < 900; k++) {
        const a = rnd() * Math.PI * 2, r = 8 + Math.abs(gauss(rnd)) * 7;
        c.globalAlpha = 0.25 + rnd() * 0.6;
        c.fillRect(32 + Math.cos(a) * r, 32 + Math.sin(a) * r, 0.9, 0.9);
      }
      this.core = core;
    },
    resize() {
      const dpr = Math.min(2, devicePixelRatio || 1);
      ui.fuga.width = innerWidth * dpr;
      ui.fuga.height = innerHeight * dpr;
      this.dpr = dpr;
      this.rect = ui.canvas.getBoundingClientRect();
    },
    spawn(px) {
      const R = this.rect, cx = R.left + R.width / 2, cy = R.top + R.height / 2;
      for (let y = 0; y < 9; y++) {
        for (let x = 0; x < 16; x++) {
          // il colore esce solo dal bordo della membrana
          if (x > 0 && x < 15 && y > 0 && y < 8) continue;
          const a = px[(y * 16 + x) * 4 + 3] / 255;
          if (a < 0.3 || Math.random() > a * 0.035 || this.parts.length > 60) continue;
          const r = 8 - y;
          const sx = R.left + ((x + 0.5) / 16) * R.width, sy = R.top + ((r + 0.5) / 9) * R.height;
          let dx = sx - cx, dy = sy - cy;
          const d = Math.hypot(dx, dy) || 1;
          const v = 0.25 + Math.random() * 0.9;
          this.parts.push({ x: sx, y: sy, vx: (dx / d) * v, vy: (dy / d) * v, r: 5 + a * 8, g: 0.1 + Math.random() * 0.22, life: 1, dec: 0.004 + Math.random() * 0.005, core: Math.random() < 0.55 });
        }
      }
    },
    splat(x, y) {
      for (let k = 0; k < 3; k++) {
        this.parts.push({ x, y, vx: (Math.random() - 0.5) * 1.6, vy: (Math.random() - 0.5) * 1.6, r: 3, g: 0.12, life: 1, dec: 0.008, core: true, nera: true });
      }
    },
    draw() {
      const c = this.ctx, d = this.dpr;
      c.setTransform(1, 0, 0, 1, 0, 0);
      c.clearRect(0, 0, ui.fuga.width, ui.fuga.height);
      c.setTransform(d, 0, 0, d, 0, 0);
      const keep = [];
      for (const p of this.parts) {
        p.x += p.vx; p.y += p.vy; p.vx *= 0.995; p.vy *= 0.995;
        p.r += p.g; p.life -= p.dec;
        if (p.life <= 0) continue;
        keep.push(p);
        c.globalAlpha = Math.min(1, p.life * 1.6);
        if (!p.nera) c.drawImage(this.glow, p.x - p.r * 2.2, p.y - p.r * 2.2, p.r * 4.4, p.r * 4.4);
        if (p.core) { const k = p.nera ? p.r * 2 : p.r * 0.9; c.drawImage(this.core, p.x - k, p.y - k, k * 2, k * 2); }
      }
      this.parts = keep;
      c.globalAlpha = 1;
    },
  };
  function gauss(rnd) { return Math.sqrt(-2 * Math.log(rnd() + 1e-9)) * Math.cos(2 * Math.PI * rnd()); }

  // ------------------------------------------------------------------ titolo, icona, indirizzo
  const titolo = {
    base: 'membrana', chars: 'membrana'.split(''), last: 0,
    ferisci(data, at) {
      for (const a of at.slice(0, 2)) {
        const v = data[a];
        this.chars[(Math.random() * this.chars.length) | 0] = v >= 33 && v < 127 ? String.fromCharCode(v) : '�';
      }
    },
    tick(now) {
      if (now - this.last < 220) return;
      this.last = now;
      if (this.eof) { document.title = 'membrana [eof]'; return; }
      if (document.hidden) { document.title = 'membrana marcisce'; return; }
      for (let k = 0; k < this.chars.length; k++) if (Math.random() < 0.12) this.chars[k] = this.base[k];
      document.title = this.chars.join('');
    },
  };
  const icona = {
    c: null, last: 0,
    tick(px, now) {
      if (now - this.last < 500) return;
      this.last = now;
      if (!this.c) { this.c = document.createElement('canvas'); this.c.width = this.c.height = 16; }
      const x2 = this.c.getContext('2d');
      x2.fillStyle = '#fff';
      x2.fillRect(0, 0, 16, 16);
      for (let y = 0; y < 9; y++) for (let x = 0; x < 16; x++) {
        const a = px[(y * 16 + x) * 4 + 3] / 255;
        if (a < 0.08) continue;
        x2.fillStyle = a > 0.7 ? '#000' : 'rgb(200,240,60)';
        x2.fillRect(x, 3 + (8 - y), 1, 1);
      }
      ui.icona.href = this.c.toDataURL('image/png');
    },
  };

  // ------------------------------------------------------------------ righe di stato
  const pad = (n, k) => String(n).padStart(k, '0');
  function stato(t) {
    const b = barOf(Math.max(0, t));
    const m = Math.floor(t / 60), s = (t % 60).toFixed(1).padStart(4, '0');
    ui.stato.textContent =
      `membrana  b${pad(b + 1, 2)}/${S.nbars}  f${pad(curF, 4)}/${frames.length}  ${m}:${s}\n` +
      `dec ${stat.decoded}  -key ${stat.keysLost}  xor ${stat.bytes}  crash ${stat.crashes}  skip ${stat.skipped}  ` +
      `col ${stat.shown ? Math.round((stat.colorFrames / stat.shown) * 100) : 0}%` +
      (mosh.amnesia ? '  senza memoria' : '') + (t >= S.protect ? '  chiusa' : '');
  }

  const GLYPH = ' ▁▂▃▄▅▆▇█';
  let partEls = [];
  function buildPartitura() {
    ui.partitura.textContent = '';
    partEls = [];
    for (let b = 0; b < S.nbars; b++) {
      const sp = document.createElement('span');
      const prot = b * S.bar >= S.protect - 0.01;
      sp.textContent = prot ? '·' : S.dropSet.has(b) ? '×' : GLYPH[Math.max(1, Math.round((S.q[b] / 24) * 8))];
      sp.title = `b${b + 1}`;
      sp.addEventListener('click', e => { e.stopPropagation(); salta(b); });
      ui.partitura.appendChild(sp);
      partEls.push(sp);
      barErr[b] = 0;
    }
  }
  let curBar = -1;
  function markBar(b) {
    if (b === curBar) return;
    if (curBar >= 0) partEls[curBar].classList.remove('o');
    partEls[b].classList.add('o', 's');
    curBar = b;
    history.replaceState(null, '', `#b${b + 1}`);
  }

  // ------------------------------------------------------------------ esploso (tasto e)
  const P = { S: 0.6, ang: Math.PI / 6, SQ: 0.5, CX: 190, CY0: 92, GAP: 112 };
  const proj = (u, v, k) => {
    const uc = u - W / 2, vc = v - H / 2, c = Math.cos(P.ang), s = Math.sin(P.ang);
    return [P.CX + P.S * (c * uc - s * vc), P.CY0 + k * P.GAP + P.S * P.SQ * (s * uc + c * vc)];
  };
  const STRATI = [
    ['s-flusso', 'partizioni dct'],
    ['s-a', 'copia a'],
    ['s-b', 'copia b'],
    ['s-danno', 'danno'],
    ['s-membrana', 'membrana'],
  ];
  const layers = {};
  function buildPalco() {
    const c = Math.cos(P.ang), s = Math.sin(P.ang);
    const m = `matrix(${P.S * c}, ${P.S * P.SQ * s}, ${-P.S * s}, ${P.S * P.SQ * c}, 0, 0)`;
    STRATI.forEach(([id], k) => {
      const el = document.getElementById(id);
      el.style.left = `${P.CX - W / 2}px`;
      el.style.top = `${P.CY0 + k * P.GAP - H / 2}px`;
      el.style.transform = m;
      el.style.zIndex = String(10 - k);
    });
    layers.a = $('#s-a').getContext('2d');
    layers.b = $('#s-b').getContext('2d');
    layers.d = $('#s-danno').getContext('2d');
    layers.m = $('#s-membrana').getContext('2d');
    layers.f = $('#s-flusso').getContext('2d');
    const NS = 'http://www.w3.org/2000/svg';
    const el = (n, a) => { const e = document.createElementNS(NS, n); for (const k in a) e.setAttribute(k, a[k]); return e; };
    const svg = ui.disegno;
    svg.textContent = '';
    const corners = [[0, 0], [W, 0], [W, H], [0, H]];
    STRATI.forEach(([, label], k) => {
      const pts = corners.map(([u, v]) => proj(u, v, k).join(',')).join(' ');
      svg.appendChild(el('polygon', { points: pts, fill: 'none', stroke: '#000', 'stroke-width': 0.8, 'stroke-dasharray': '4 3', class: k === 0 ? 'piano0' : '' }));
      const [rx, ry] = proj(W, 0, k);
      svg.appendChild(el('line', { x1: rx + 6, y1: ry, x2: 392, y2: ry, stroke: '#000', 'stroke-width': 0.8 }));
      svg.appendChild(el('rect', { x: 392, y: ry - 2.5, width: 5, height: 5, fill: '#000' }));
      const t = el('text', { x: 404, y: ry + 5 });
      t.textContent = label;
      svg.appendChild(t);
    });
    for (const [u, v] of [[0, 0], [W, 0], [W, H], [0, H], [W * 0.31, H * 0.42], [W * 0.66, H * 0.3], [W * 0.5, H * 0.77]]) {
      const [x1, y1] = proj(u, v, 0), [, y2] = proj(u, v, 4);
      svg.appendChild(el('line', { x1, y1, x2: x1, y2, stroke: '#000', 'stroke-width': 0.6, 'stroke-dasharray': '1.5 3' }));
      svg.appendChild(el('circle', { cx: x1, cy: y1, r: 2.4, fill: '#fff', stroke: '#000', 'stroke-width': 0.8 }));
    }
    layers.hits = el('g', {});
    svg.appendChild(layers.hits);
    fitPalco();
  }
  function fitPalco() {
    const k = Math.min(innerWidth / 600, (innerHeight - 70) / 680);
    ui.palcoIn.style.transform = `translate(-50%, -50%) scale(${k})`;
  }
  function drawFlusso(now) {
    const c = layers.f;
    c.clearRect(0, 0, W, H);
    c.strokeStyle = '#000';
    c.globalAlpha = 0.35;
    c.lineWidth = 1;
    c.setLineDash([2, 3]);
    c.beginPath();
    for (let x = 0; x <= W; x += 16) { c.moveTo(x + 0.5, 0); c.lineTo(x + 0.5, H); }
    for (let y = 0; y <= H; y += 16) { c.moveTo(0, y + 0.5); c.lineTo(W, y + 0.5); }
    c.stroke();
    c.setLineDash([]);
    // la riga toccata, e le righe della stessa partizione più in basso: lì il decoder ha perso il filo
    for (const h of flips) {
      const age = (now - h.t) / 1200;
      if (age > 1) continue;
      c.globalAlpha = 1 - age;
      const col = Math.floor(h.x * MB_COLS);
      for (let r = h.row; r < MB_ROWS; r += NPART) {
        const x0 = r === h.row ? col * 16 : 0, y0 = r * 16;
        c.save();
        c.beginPath(); c.rect(x0, y0, W - x0, 16); c.clip();
        c.beginPath();
        for (let d = -16; d < W + 16; d += 4) { c.moveTo(d, y0 + 16); c.lineTo(d + 16, y0); }
        c.lineWidth = 1;
        c.stroke();
        c.restore();
      }
      c.lineWidth = 1.5;
      c.beginPath();
      const px = col * 16 + 8, py = h.row * 16 + 8;
      c.moveTo(px - 5, py); c.lineTo(px + 5, py); c.moveTo(px, py - 5); c.lineTo(px, py + 5);
      c.stroke();
    }
    c.globalAlpha = 1;
    // linee verticali che attraversano tutti gli strati nel punto riscritto
    const g = layers.hits;
    g.textContent = '';
    const NS = 'http://www.w3.org/2000/svg';
    for (const h of flips.slice(-8)) {
      if (now - h.t > 1200) continue;
      const u = (Math.floor(h.x * MB_COLS) + 0.5) * 16, v = (h.row + 0.5) * 16;
      const [x1, y1] = proj(u, v, 0), [, y2] = proj(u, v, 4);
      const ln = document.createElementNS(NS, 'line');
      ln.setAttribute('x1', x1); ln.setAttribute('x2', x1); ln.setAttribute('y1', y1); ln.setAttribute('y2', y2);
      ln.setAttribute('stroke', '#000'); ln.setAttribute('stroke-width', '0.9');
      g.appendChild(ln);
      const tx = document.createElementNS(NS, 'text');
      tx.setAttribute('x', x1 + 4); tx.setAttribute('y', y1 - 4);
      tx.style.fontStyle = 'normal'; tx.style.fontSize = '9px'; tx.style.fontFamily = 'Courier New, monospace';
      tx.textContent = `0x${h.at.toString(16)}`;
      g.appendChild(tx);
    }
    ui.disegno.querySelector('.piano0').setAttribute('stroke-width', now - lostAt < 500 ? 2.4 : 0.8);
  }
  let lostAt = -1e9;

  function toggleEsploso(on) {
    esploso = on == null ? !esploso : on;
    ui.palco.hidden = !esploso;
    ui.schermo.classList.toggle('spento', esploso);
    if (esploso) { fitPalco(); lastF = -1; }
  }

  // ------------------------------------------------------------------ lettura del danno
  const rows = [new Float32Array(9), new Float32Array(9)];
  function applyStats(px, t) {
    let sa = 0;
    rows[0].fill(0); rows[1].fill(0);
    for (let y = 0; y < 9; y++) {
      const r = 8 - y;
      for (let x = 0; x < 16; x++) {
        const a = px[(y * 16 + x) * 4 + 3] / 255;
        sa += a;
        rows[x < 8 ? 0 : 1][r] += a / 8;
      }
    }
    const tot = sa / 144;
    stat.shown++;
    if (tot > 0.004) {
      stat.colorFrames++;
      const b = barOf(t);
      barErr[b]++;
      if (barErr[b] > 3) partEls[b].classList.add('e');
    }
    sound.damage(rows);
    fuga.spawn(px);
  }

  // ------------------------------------------------------------------ ciclo
  let lastKeyLost = 0;
  function tick() {
    const now = performance.now();
    fuga.draw();
    titolo.tick(now);
    if (!running) return;
    const t = sound.time();
    if (t >= DUR - 0.05) { fine(); return; }
    const f = Math.max(0, Math.floor(t * FPS));
    feedA(f);
    feedB(f);
    if (stat.keysLost !== lastKeyLost) { lastKeyLost = stat.keysLost; lostAt = now; }
    const a = A.pick(f), b = B.pick(f);
    if (f !== lastF && a && b) {
      lastF = f;
      curF = f;
      if (a.f !== gfx.lastA) { gfx.upload(gfx.tA, a.f); gfx.lastA = a.f; }
      if (b.f !== gfx.lastB) { gfx.upload(gfx.tB, b.f); gfx.lastB = b.f; }
      const px = gfx.run(t >= S.protect, esploso ? layers : null);
      applyStats(px, t);
      icona.tick(px, now);
      markBar(barOf(t));
      dump.draw(Math.min(frames.length - 1, B.next - 1), lastData, lastFlipAt);
      stato(t);
      if (esploso) drawFlusso(now);
    }
  }

  function avvia(offset) {
    lastF = -1;
    A.make(); A.dropAll(); A.next = keyBefore(Math.floor(offset * FPS));
    B.make(); B.dropAll(); B.next = A.next; B.fresh = true;
    mosh.bloomUntil = -1; mosh.freezing = false; mosh.amnesia = false;
    gfx.clear();
    sound.play(offset);
    running = true;
    titolo.eof = false;
    ui.entra.hidden = true;
    ui.schermo.classList.remove('spento');
    ui.canvas.focus({ preventScroll: true });
  }

  // salto: A riparte pulito, B no, e il movimento nuovo si posa sull'immagine vecchia
  function salta(b) {
    if (!S || !frames) return;
    b = Math.max(0, Math.min(S.nbars - 1, b));
    if (sound.ctx.state === 'suspended') sound.ctx.resume();
    const off = b * S.bar;
    if (!running) { avvia(off); return; }
    const f = Math.floor(off * FPS);
    sound.play(off);
    A.make(); A.dropAll(); A.next = keyBefore(f);
    if (B.needKey) B.next = keyBefore(f); else { B.rebase(f); B.next = f + 1; }
    lastF = -1;
    sound.colata(off);
  }

  function fine() {
    running = false;
    sound.stop();
    sound.off = 0;
    dump.text(('EOF ').repeat(Math.ceil(dump.cap * 0.75) + 400));
    ui.stato.textContent += '\neof';
    ui.entra.hidden = false;
    titolo.eof = true;
    history.replaceState(null, '', location.pathname + location.search);
  }

  function salvaFotogramma() {
    const c = document.createElement('canvas');
    c.width = W * 4; c.height = H * 4;
    const x2 = c.getContext('2d');
    x2.imageSmoothingEnabled = false;
    x2.drawImage(ui.canvas, 0, 0, c.width, c.height);
    c.toBlob(blob => {
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = `membrana_f${pad(curF, 4)}_xor${stat.bytes}_crash${stat.crashes}.png`;
      a.click();
      setTimeout(() => URL.revokeObjectURL(a.href), 2000);
    });
  }

  // ------------------------------------------------------------------ cursore: l'ultimo byte riscritto
  const cursore = {
    x: 0, y: 0, until: 0,
    move(e) { this.x = e.clientX; this.y = e.clientY; this.place(); },
    place() { ui.cursore.style.left = `${this.x + 14}px`; ui.cursore.style.top = `${this.y + 10}px`; },
    mostra(at, v) {
      ui.cursore.textContent = `0x${at.toString(16).padStart(5, '0')} ${hex[v]}`;
      ui.cursore.style.display = 'block';
      clearTimeout(this.tm);
      this.tm = setTimeout(() => { ui.cursore.style.display = 'none'; }, 700);
    },
  };

  // ------------------------------------------------------------------ gesti, tasti, uova
  function bindGestures() {
    const cv = ui.canvas;
    let last = null;
    const rel = e => {
      const r = cv.getBoundingClientRect();
      return { x: Math.min(1, Math.max(0, (e.clientX - r.left) / r.width)), y: Math.min(1, Math.max(0, (e.clientY - r.top) / r.height)) };
    };
    addEventListener('pointermove', e => cursore.move(e));
    cv.addEventListener('pointerdown', e => {
      if (!running) return;
      try { cv.setPointerCapture(e.pointerId); } catch (err) { /* puntatore sintetico */ }
      mosh.hold = true;
      mosh.holdSrc = -1;
      last = { x: e.clientX, y: e.clientY };
      mosh.pos = rel(e);
    });
    cv.addEventListener('pointermove', e => {
      if (!running || !last) return;
      const d = Math.hypot(e.clientX - last.x, e.clientY - last.y);
      last = { x: e.clientX, y: e.clientY };
      mosh.pos = rel(e);
      mosh.drag = Math.min(64, mosh.drag + d / 7);
      if (Math.random() < 0.15) fuga.splat(e.clientX, e.clientY);
    });
    const up = () => { mosh.hold = false; mosh.holdSrc = -1; last = null; };
    cv.addEventListener('pointerup', up);
    cv.addEventListener('pointercancel', up);
    cv.addEventListener('contextmenu', e => { e.preventDefault(); if (running) salvaFotogramma(); });
    cv.addEventListener('dblclick', () => { document.fullscreenElement ? document.exitFullscreen() : document.documentElement.requestFullscreen().catch(() => {}); });

    // rotella: graffiare il tempo
    let wheel = 0;
    cv.addEventListener('wheel', e => {
      if (!running) return;
      e.preventDefault();
      wheel += e.deltaY;
      if (Math.abs(wheel) >= 120) { salta(barOf(sound.time()) + Math.sign(wheel)); wheel = 0; }
    }, { passive: false });

    // stirare la finestra stira la membrana
    let lw = innerWidth, lh = innerHeight;
    addEventListener('resize', () => {
      const d = Math.abs(innerWidth - lw) + Math.abs(innerHeight - lh);
      lw = innerWidth; lh = innerHeight;
      if (running && innerWidth > 0) { mosh.pos = { x: Math.random(), y: Math.random() }; mosh.drag = Math.min(64, mosh.drag + d / 6); }
      fuga.resize(); dump.measure(); fitPalco();
    });

    // tornare dopo essere andati via
    document.addEventListener('visibilitychange', () => { titolo.last = 0; titolo.tick(performance.now()); });

    // copiare: la membrana si mangia gli appunti
    document.addEventListener('copy', e => {
      if (!frames) return;
      const fr = frames[Math.max(0, curF)];
      let s = '';
      for (let k = 0; k < Math.min(fr.data.length, 512); k++) s += hex[fr.data[k]] + (k % 16 === 15 ? '\n' : ' ');
      e.clipboardData.setData('text/plain', `${s}\n-- membrana f${curF}`);
      e.preventDefault();
    });

    const kpos = { x: 0.5, y: 0.5 };
    const KONAMI = ['ArrowUp', 'ArrowUp', 'ArrowDown', 'ArrowDown', 'ArrowLeft', 'ArrowRight', 'ArrowLeft', 'ArrowRight', 'b', 'a'];
    let seq = [], typed = '';
    addEventListener('keydown', e => {
      if (e.ctrlKey || e.metaKey || e.altKey) return;
      seq = [...seq, e.key].slice(-10);
      if (seq.join() === KONAMI.join() && running) { mosh.amnesia = true; console.log('%csenza memoria', 'background:#c8f03c'); }
      if (e.key.length === 1) {
        typed = (typed + e.key.toLowerCase()).slice(-12);
        if (typed.endsWith('embrione')) salta(62);
        if (typed.endsWith('jodi')) document.documentElement.classList.toggle('jodi');
      }
      if (!running && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); entra(); return; }
      if (!running) return;
      const step = { ArrowLeft: [-0.06, 0], ArrowRight: [0.06, 0], ArrowUp: [0, -0.08], ArrowDown: [0, 0.08] }[e.key];
      if (step) {
        e.preventDefault();
        kpos.x = Math.min(1, Math.max(0, kpos.x + step[0]));
        kpos.y = Math.min(1, Math.max(0, kpos.y + step[1]));
        mosh.pos = { ...kpos };
        mosh.drag = Math.min(64, mosh.drag + 10);
        return;
      }
      switch (e.key) {
        case ' ': e.preventDefault(); if (!mosh.hold) { mosh.hold = true; mosh.holdSrc = -1; } break;
        // lettere scelte fuori da 'embrione' e 'jodi'
        case 'k': mosh.forget = true; break;
        case 'z': mosh.recall = keyIdx[(Math.random() * (barOf(sound.time()) + 1)) | 0]; break;
        case 'g': mosh.recall = keyBefore(curF + 1); mosh.amnesia = false; break;
        case 'x': toggleEsploso(); break;
        case 's': salvaFotogramma(); break;
        case 'f': document.fullscreenElement ? document.exitFullscreen() : document.documentElement.requestFullscreen().catch(() => {}); break;
        case 'v': document.documentElement.classList.toggle('inv'); break;
        default:
          if (/^[1-6]$/.test(e.key)) salta(S.sections[+e.key - 1][1]);
      }
    });
    addEventListener('keyup', e => { if (e.key === ' ') up(); });
    ui.stato.addEventListener('click', () => { if (running) toggleEsploso(); });
  }

  // ------------------------------------------------------------------ console
  function console_() {
    const art = (document.documentElement.innerHTML.match(/<!--([\s\S]*?)-->/) || [, ''])[1];
    console.log(`%c${art}`, 'font: 9px/9px monospace; color: #000; background: #c8f03c');
    console.log('%cmembrana.aiuto()', 'font: 12px monospace');
    console.log('il brano  https://smollojames.bandcamp.com/track/membrana\nil film   https://youtu.be/9Lv9OIGGwyE');
    window.membrana = {
      aiuto() {
        console.log([
          'membrana.rompi(n)      riscrive n byte nel prossimo fotogramma',
          'membrana.dimentica()   il prossimo fotogramma chiave non arriva',
          'membrana.ricorda(b)    il decoder riparte dalla battuta b',
          'membrana.guarisci()    il decoder riparte dalla battuta giusta',
          'membrana.salta(b)      vai alla battuta b',
          'membrana.esploso()     separa gli strati',
          'membrana.stato()       i conti',
          'membrana.ascolta()     il brano, su bandcamp',
        ].join('\n'));
      },
      rompi(n = 32) { mosh.pos = { x: Math.random(), y: Math.random() }; mosh.drag = Math.min(64, mosh.drag + n); return n; },
      dimentica() { mosh.forget = true; return 'ok'; },
      ricorda(b = 0) { mosh.recall = keyIdx[Math.max(0, Math.min(keyIdx.length - 1, b - 1))]; return b; },
      guarisci() { mosh.recall = keyBefore(curF + 1); mosh.amnesia = false; return 'ok'; },
      salta(b = 1) { salta(b - 1); return b; },
      esploso() { toggleEsploso(); return esploso; },
      stato() { return { ...stat, f: curF }; },
      ascolta() { window.open('https://smollojames.bandcamp.com/track/membrana', '_blank'); return 'https://smollojames.bandcamp.com/track/membrana'; },
    };
    if (location.search.includes('debug')) window.__membrana = { sound, stat, mosh, get A() { return A; }, get B() { return B; }, get S() { return S; } };
  }

  // ------------------------------------------------------------------ avvio
  function entra() {
    if (!frames || !S || running) return;
    const resume = sound.ctx.state === 'suspended' ? sound.ctx.resume() : Promise.resolve();
    resume.then(() => {
      const m = location.hash.match(/^#b(\d+)$/);
      avvia(m ? Math.max(0, Math.min(S.nbars - 1, +m[1] - 1)) * S.bar : 0);
    });
  }

  function errore(msg) {
    ui.stato.textContent = msg;
    dump.text((msg + ' ').repeat(400));
    ui.entra.textContent = 'versione fissa';
    ui.entra.href = 'assets/membrana_fissa.mp4';
    ui.entra.hidden = false;
  }

  async function boot() {
    ui.entra.hidden = true;
    dump.measure();
    fuga.init();
    setInterval(tick, 1000 / 60);
    if (!('VideoDecoder' in window) || !('EncodedVideoChunk' in window)) { errore('VideoDecoder is not defined'); return; }
    const base = { codec: 'vp8', codedWidth: W, codedHeight: H };
    try {
      const sw = await VideoDecoder.isConfigSupported({ ...base, hardwareAcceleration: 'prefer-software' });
      if (sw.supported) CFG = { ...base, hardwareAcceleration: 'prefer-software' };
      else if ((await VideoDecoder.isConfigSupported(base)).supported) CFG = base;
    } catch (e) { CFG = null; }
    if (!CFG) { errore("NotSupportedError: codec 'vp8'"); return; }
    if (!gfx.init(ui.canvas)) { errore('webgl2: null'); return; }
    const [score, buf, mp3] = await Promise.all([
      fetch('assets/score.json').then(r => r.json()),
      fetch('assets/film.ivf').then(r => r.arrayBuffer()),
      fetch('assets/membrana.mp3').then(r => r.arrayBuffer()),
    ]);
    S = score;
    S.dropSet = new Set(S.drop);
    S.corruptSet = new Set(S.corrupt);
    S.bloomAt = new Map(S.blooms.map(([k, L]) => [k, L]));
    film = new Uint8Array(buf);
    frames = parseIVF(buf);
    keyIdx = frames.map((f, i) => (f.key ? i : -1)).filter(i => i >= 0);
    buildPartitura();
    buildPalco();
    await sound.init(mp3);
    DUR = Math.min(sound.buf.duration, frames.length / FPS);
    A = new Dec('A');
    B = new Dec('B');
    bindGestures();
    console_();
    // prima di entrare: l'intestazione del file e il primo fotogramma chiave, così come arrivano
    const dv = new DataView(buf);
    ui.stato.textContent = `DKIF VP80 ${dv.getUint16(12, true)}x${dv.getUint16(14, true)} ${dv.getUint32(16, true)}/${dv.getUint32(20, true)} ${frames.length}f ${(buf.byteLength / 1048576).toFixed(1)}MB`;
    dump.draw(0, null, []);
    ui.schermo.classList.add('spento');
    ui.entra.hidden = false;
    ui.entra.addEventListener('click', e => { e.preventDefault(); entra(); });
    addEventListener('pointerdown', e => { if (!running && e.target !== ui.entra && !ui.partitura.contains(e.target) && !e.target.closest('#crediti')) entra(); });
  }

  boot().catch(e => { console.error(e); errore(String(e && e.message || e)); });
})();
