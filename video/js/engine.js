/* The Third Logarithm: timeline engine and player.
 *
 * The video is a pure function of time: draw(t) must not read wall clocks or keep state, so seeking
 * is exact. A scene is a list of narration "beats"; beat durations come from word counts, and every
 * animation is written relative to its beat so it cannot drift from the sentence it belongs to.
 * Interactive scenes may add a small `ix` state object, layered on top and never touched by seeking.
 */
(function () {
  'use strict';
  const V = (window.V = {});
  const W = 1280, H = 720;
  V.W = W; V.H = H;
  V.chapters = []; V.scenes = [];
  let curCh = null;

  V.part = (title) => { V.nextPart = title; };
  V.chapter = (id, title, opts = {}) => {
    curCh = { id, title, part: V.nextPart || '', scenes: [], ...opts };
    V.nextPart = null;
    V.chapters.push(curCh);
    return curCh;
  };
  V.scene = (spec) => { spec.ch = curCh; curCh.scenes.push(spec); V.scenes.push(spec); };

  // ---------------------------------------------------------------------- reduced motion
  const rmQuery = window.matchMedia ? matchMedia('(prefers-reduced-motion: reduce)') : null;
  V.RM = !!(rmQuery && rmQuery.matches);
  if (rmQuery && rmQuery.addEventListener) rmQuery.addEventListener('change', (e) => { V.RM = e.matches; invalidate(); });

  const clamp = (x, a = 0, b = 1) => (x < a ? a : x > b ? b : x);
  const smooth = (u) => u * u * (3 - 2 * u);
  V.ease = (u) => (V.RM ? (u >= 0.5 ? 1 : 0) : smooth(clamp(u)));
  V.lerp = (a, b, u) => a + (b - a) * u;
  V.clamp = clamp;

  // ---------------------------------------------------------------------- durations
  const WPS = 2.9;                       // words per second for pacing captions at comfortable reading speed
  const MIN_BEAT = 1.5, GAP = 0.3;
  function layout() {
    let t = 0;
    for (const sc of V.scenes) {
      sc.T0 = t;
      sc.beats = (sc.beats || []).map((b) => (typeof b === 'string' ? { say: b } : b));
      let u = sc.pre || 0.45;
      sc.beats.forEach((b) => {
        const words = (b.say || '').trim().split(/\s+/).filter(Boolean).length;
        const dur = (b.dur != null ? b.dur : Math.max(MIN_BEAT, words / WPS)) + (b.hold || 0) + GAP;
        b.t0 = u; b.t1 = u + dur; b.d = dur; u += dur;
      });
      sc.D = u + (sc.post != null ? sc.post : 0.5);
      t += sc.D;
    }
    V.T = t;
    for (const ch of V.chapters) {
      ch.T0 = ch.scenes[0].T0;
      ch.T1 = ch.scenes[ch.scenes.length - 1].T0 + ch.scenes[ch.scenes.length - 1].D;
    }
  }

  function makeBeatHelper(sc, t) {
    const beats = sc.beats, n = beats.length;
    let cur = n - 1;
    for (let i = 0; i < n; i++) if (t < beats[i].t1) { cur = i; break; }
    const start = (i) => (i >= n ? sc.D : i < 0 ? 0 : beats[i].t0);
    const end = (i) => (i >= n ? sc.D : i < 0 ? 0 : beats[i].t1);
    const dur = (i) => (i < 0 || i >= n ? 1 : beats[i].d);
    return {
      t, D: sc.D, cur, n,
      s: start, e: end, d: dur,
      // progress through beat i, between fractions a and b of that beat (eased, 0..1)
      p(i, a = 0, b = 1) {
        const s = start(i), d = dur(i);
        const t0 = s + a * d, t1 = s + b * d;
        const u = clamp((t - t0) / Math.max(1e-6, t1 - t0));
        return V.RM ? (u >= 0.5 ? 1 : 0) : smooth(u);
      },
      raw(i, a = 0, b = 1) { const s = start(i), d = dur(i); return clamp((t - (s + a * d)) / Math.max(1e-6, (b - a) * d)); },
      // envelope: fades in at start of beat i, fades out at start of beat j (default: never)
      on(i, j) {
        const f = 0.45;
        let a = clamp((t - start(i)) / f);
        if (j !== undefined && j < n) a = Math.min(a, 1 - clamp((t - start(j)) / f));
        return V.RM ? (a >= 0.5 ? 1 : 0) : smooth(a);
      },
      in(i, j) { return t >= start(i) && (j === undefined || t < start(j)); },
    };
  }

  // ---------------------------------------------------------------------- canvas layer
  let cv, ctx, tx, k = 1, dpr = 1;
  const C = (V.C = {});
  function readTheme() {
    const st = getComputedStyle(document.documentElement);
    const g = (n) => st.getPropertyValue(n).trim();
    Object.assign(C, {
      bg: g('--surface'), bg2: g('--surface2'), bg3: g('--surface3'), ink: g('--ink'), ink2: g('--ink2'), ink3: g('--ink3'), rule: g('--rule'),
      blue: g('--blue'), orange: g('--orange'), aqua: g('--aqua'), yellow: g('--yellow'), mag: g('--mag'), green: g('--green'), violet: g('--violet'), red: g('--red'),
      chip: g('--chip'),
    });
    C.pos = C.blue; C.lab = C.yellow; C.x2 = C.blue; C.rho = C.orange; C.sig = C.aqua; C.Q = C.yellow; C.h = C.mag;
    C.dark = document.documentElement.dataset.theme === 'dark' ||
      (!document.documentElement.dataset.theme && matchMedia('(prefers-color-scheme: dark)').matches);
  }

  // Immediate-mode drawing, in logical 1280x720 coordinates. Shapes go to the canvas; math goes to a
  // keyed pool of KaTeX elements reconciled every frame.
  const c = (V.c = { A: 1 });
  const FS = 'system-ui,-apple-system,"Segoe UI",Roboto,"Helvetica Neue",Arial,sans-serif';
  function al(o) { return (o && o.alpha != null ? o.alpha : 1) * c.A; }
  c.ctx = () => ctx;
  c.circle = (x, y, r, o = {}) => {
    const a = al(o); if (a <= 0) return;
    ctx.globalAlpha = a; ctx.beginPath(); ctx.arc(x, y, r, 0, 2 * Math.PI);
    if (o.fill) { ctx.fillStyle = o.fill; ctx.fill(); }
    if (o.stroke) { ctx.strokeStyle = o.stroke; ctx.lineWidth = o.lw || 2; ctx.stroke(); }
    ctx.globalAlpha = 1;
  };
  c.line = (x1, y1, x2, y2, o = {}) => {
    const a = al(o); if (a <= 0) return;
    ctx.globalAlpha = a; ctx.strokeStyle = o.stroke || C.ink; ctx.lineWidth = o.lw || 2;
    ctx.lineCap = o.cap || 'round'; ctx.setLineDash(o.dash || []);
    ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke();
    ctx.setLineDash([]); ctx.globalAlpha = 1;
  };
  c.arrow = (x1, y1, x2, y2, o = {}) => {
    const a = al(o); if (a <= 0) return;
    c.line(x1, y1, x2, y2, o);
    const h = o.head || 11, ang = Math.atan2(y2 - y1, x2 - x1);
    ctx.globalAlpha = a; ctx.fillStyle = o.stroke || C.ink; ctx.beginPath(); ctx.moveTo(x2, y2);
    ctx.lineTo(x2 - h * Math.cos(ang - 0.42), y2 - h * Math.sin(ang - 0.42));
    ctx.lineTo(x2 - h * Math.cos(ang + 0.42), y2 - h * Math.sin(ang + 0.42));
    ctx.closePath(); ctx.fill(); ctx.globalAlpha = 1;
  };
  c.rect = (x, y, w, h, o = {}) => {
    const a = al(o); if (a <= 0) return;
    ctx.globalAlpha = a; ctx.beginPath();
    const r = o.r || 0;
    if (r) { if (ctx.roundRect) ctx.roundRect(x, y, w, h, r); else ctx.rect(x, y, w, h); } else ctx.rect(x, y, w, h);
    if (o.fill) { ctx.fillStyle = o.fill; ctx.fill(); }
    if (o.stroke) { ctx.strokeStyle = o.stroke; ctx.lineWidth = o.lw || 2; ctx.stroke(); }
    ctx.globalAlpha = 1;
  };
  c.poly = (pts, o = {}) => {
    const a = al(o); if (a <= 0) return;
    ctx.globalAlpha = a; ctx.beginPath(); pts.forEach((p, i) => (i ? ctx.lineTo(p[0], p[1]) : ctx.moveTo(p[0], p[1])));
    if (o.close !== false) ctx.closePath();
    if (o.fill) { ctx.fillStyle = o.fill; ctx.fill(); }
    if (o.stroke) { ctx.strokeStyle = o.stroke; ctx.lineWidth = o.lw || 2; ctx.lineJoin = 'round'; ctx.stroke(); }
    ctx.globalAlpha = 1;
  };
  c.text = (s, x, y, o = {}) => {
    const a = al(o); if (a <= 0) return;
    ctx.globalAlpha = a; ctx.fillStyle = o.fill || C.ink;
    ctx.font = `${o.italic ? 'italic ' : ''}${o.weight || 400} ${o.size || 22}px ${o.family || FS}`;
    ctx.textAlign = o.align || 'center'; ctx.textBaseline = o.base || 'middle';
    ctx.fillText(s, x, y);
    ctx.globalAlpha = 1;
  };
  c.width = (s, o = {}) => { ctx.font = `${o.weight || 400} ${o.size || 22}px ${FS}`; return ctx.measureText(s).width; };

  const txPool = new Map(), txSeen = new Set();
  c.tex = (ltx, x, y, o = {}) => {
    const a = al(o);
    const key = (o.key || '') + '|' + (o.size || 26) + '|' + ltx;
    let el = txPool.get(key);
    if (!el) {
      el = document.createElement('div'); el.className = 't'; el.style.fontSize = (o.size || 26) + 'px';
      try { katex.render(ltx, el, { throwOnError: true, displayMode: false, strict: false }); }
      catch (e) { el.textContent = 'TeX error: ' + ltx; console.error('KaTeX failed:', ltx, e.message); }
      tx.appendChild(el); txPool.set(key, el);
    }
    txSeen.add(key);
    const ax = o.align === 'left' ? 0 : o.align === 'right' ? 100 : 50, ay = o.valign === 'top' ? 0 : o.valign === 'bottom' ? 100 : 50;
    el.style.left = x + 'px'; el.style.top = y + 'px';
    el.style.transform = `translate(${-ax}%,${-ay}%)`;
    el.style.opacity = a <= 0 ? 0 : a;
    el.style.display = a <= 0 ? 'none' : '';
    el.style.color = o.fill || C.ink;
  };
  function finishFrame() { txPool.forEach((el, key) => { if (!txSeen.has(key)) el.style.display = 'none'; }); txSeen.clear(); }

  function resize() {
    const wrap = document.getElementById('stage-wrap');
    const stage = document.getElementById('stage');
    const rect = wrap.getBoundingClientRect();
    let ww = rect.width, hh = rect.height;
    const portrait = window.innerWidth <= 760 && window.innerHeight > window.innerWidth;
    if (portrait) hh = Math.min(ww * 9 / 16, window.innerHeight * 0.45);
    k = Math.min(ww / W, hh / H);
    const cw = Math.round(W * k), ch = Math.round(H * k);
    stage.style.width = cw + 'px'; stage.style.height = ch + 'px';
    if (portrait) wrap.style.height = ch + 'px'; else wrap.style.height = '';
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    cv.width = Math.round(cw * dpr); cv.height = Math.round(ch * dpr);
    tx.style.transform = `scale(${k})`;
    invalidate();
  }
  function toStage(cx, cy) {
    const r = cv.getBoundingClientRect();
    return [(cx - r.left) / r.width * W, (cy - r.top) / r.height * H];
  }

  // ---------------------------------------------------------------------- player state
  const P = (V.P = { t: 0, playing: false, speed: 1, voice: false, dirty: true });
  let last = 0, held = false, ixBuilt = new Map(), curScene = null, sceneIdx = 0;

  function sceneAt(t) {
    let lo = 0, hi = V.scenes.length - 1;
    while (lo < hi) { const m = (lo + hi + 1) >> 1; if (V.scenes[m].T0 <= t) lo = m; else hi = m - 1; }
    return lo;
  }
  function invalidate() { P.dirty = true; }
  V.invalidate = invalidate;

  function render() {
    const i = sceneAt(P.t);
    const sc = V.scenes[i];
    if (i !== sceneIdx || sc !== curScene) { enterScene(i, sc); }
    const local = clamp(P.t - sc.T0, 0, sc.D);
    const b = makeBeatHelper(sc, local);
    ctx.setTransform(k * dpr, 0, 0, k * dpr, 0, 0);
    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = C.bg; ctx.fillRect(0, 0, W, H);
    c.A = 1;
    const fade = 0.35;
    if (!V.RM) {
      const env = Math.min(clamp(local / fade), clamp((sc.D - local) / fade));
      c.A = smooth(env);
    } else if (local < 0 || local > sc.D) c.A = 0;
    sc.draw(c, b, sc.ix || (sc.ix = (sc.init ? sc.init() : {})));
    finishFrame();
    // caption
    const beat = sc.beats[b.cur];
    const textOut = beat ? beat.say : '';
    if (P.caption !== textOut) { P.caption = textOut; document.getElementById('caption-text').textContent = textOut; }
    updateChrome(i, sc, local, b);
  }

  function enterScene(i, sc) {
    if (curScene && curScene.ixEl) curScene.ixEl.remove();
    if (curScene && curScene.onLeave) curScene.onLeave(curScene.ix);
    sceneIdx = i; curScene = sc;
    if (sc.buildUI) {
      const box = document.getElementById('ix');
      const holder = document.createElement('div'); holder.style.position = 'absolute'; holder.style.inset = '0';
      box.innerHTML = ''; box.appendChild(holder);
      sc.ix = sc.ix || (sc.init ? sc.init() : {});
      sc.buildUI(holder, sc.ix, invalidate, () => { pauseIfPlaying(); invalidate(); });
      sc.ixEl = holder;
    } else {
      document.getElementById('ix').innerHTML = '';
    }
    // stage click routing
    cv.style.cursor = sc.onClick ? 'pointer' : 'default';
  }

  function updateChrome(i, sc, local, b) {
    const tEl = document.getElementById('tm');
    const fmt = (x) => { const m = Math.floor(x / 60), s = Math.floor(x % 60); return m + ':' + String(s).padStart(2, '0'); };
    tEl.textContent = fmt(P.t) + ' / ' + fmt(V.T);
    const u = P.t / V.T;
    document.getElementById('track-fill').style.width = (u * 100).toFixed(3) + '%';
    document.getElementById('track-handle').style.left = (u * 100).toFixed(3) + '%';
    const tr = document.getElementById('track');
    tr.setAttribute('aria-valuenow', Math.round(u * 100));
    tr.setAttribute('aria-valuetext', fmt(P.t) + ' of ' + fmt(V.T) + ': ' + sc.ch.title);
    const hash = '#ch=' + sc.ch.id;
    if (location.hash.startsWith('#ch=') && location.hash !== hash && !P.suppressHash) {
      try { history.replaceState(null, '', hash); } catch (e) { /* file:// restrictions */ }
    }
    document.querySelectorAll('.chap').forEach((b2) => b2.classList.toggle('cur', b2.dataset.ch === sc.ch.id));
  }

  function setPlaying(p) {
    P.playing = p;
    document.getElementById('pp-icon').setAttribute('d', p ? 'M6 5h4v14H6zm8 0h4v14h-4z' : 'M8 5v14l11-7z');
    document.getElementById('big-play').hidden = p || P.everPlayed;
    if (p) P.everPlayed = true;
    if (!p) cancelSpeech();
    invalidate();
  }
  function pauseIfPlaying() { if (P.playing) setPlaying(false); }
  V.seek = (t, keepPlaying) => {
    P.t = clamp(t, 0, V.T - 0.001);
    cancelSpeech(); held = false; P.spokenBeat = null;
    if (!keepPlaying) invalidate();
    invalidate();
  };

  // ---------------------------------------------------------------------- speech (optional)
  const synth = window.speechSynthesis || null;
  const SPOKEN = [['Ω', ' omega '], ['Γ̂', ' gamma hat '], ['Γ', ' gamma '], ['σ', ' sigma '], ['ρ', ' rho '], ['κ', ' kappa '],
    ['Φ', ' phi '], ['λ', ' lambda '], ['α', ' alpha '], ['γ', ' gamma '], ['θ', ' theta '], ['β', ' beta '], ['η', ' eta '],
    ['δ', ' delta '], ['Λ', ' lambda '], ['ρ', ' rho '], ['²', ' squared '], ['³', ' cubed '], ['≤', ' at most '], ['≥', ' at least '],
    ['×', ' times '], ['·', ' times '], ['√', ' square root of '], ['→', ' goes to '], ['∈', ' in '], ['log n', 'log n'],
    ['Φ_Λ', 'phi lambda']];
  function spoken(s) { for (const [a, b] of SPOKEN) s = s.split(a).join(b); return s.replace(/\s+/g, ' ').trim(); }
  function voicesReady() { return synth && synth.getVoices && synth.getVoices().length > 0; }
  function cancelSpeech() { if (synth) { synth.cancel(); } P.utt = null; P.spokenBeat = null; }
  function maybeSpeak(sc, b) {
    if (!P.voice || !synth || !P.playing) return;
    const id = sc.T0 + ':' + b.cur;
    if (P.spokenBeat === id) return;
    P.spokenBeat = id;
    synth.cancel();
    const beat = sc.beats[b.cur]; if (!beat || !beat.say) return;
    const u = new SpeechSynthesisUtterance(spoken(beat.say));
    u.rate = Math.min(2, 0.98 * P.speed);
    u.onend = () => { if (P.utt === u) { P.utt = null; } };
    u.onerror = () => { if (P.utt === u) { P.utt = null; } };
    P.utt = u;
    synth.speak(u);
  }
  function toggleVoice() {
    if (!synth) { flash('Speech synthesis is not available in this browser.'); return; }
    if (!P.voice && !voicesReady()) {
      // some browsers load voices lazily; try anyway
      synth.getVoices();
    }
    P.voice = !P.voice;
    const b = document.getElementById('voice');
    b.textContent = P.voice ? 'Voice on' : 'Voice off';
    b.setAttribute('aria-pressed', P.voice ? 'true' : 'false');
    if (!P.voice) cancelSpeech();
    P.spokenBeat = null;
  }
  function flash(msg) { document.getElementById('caption-text').textContent = msg; P.caption = msg; }

  // ---------------------------------------------------------------------- frame loop
  function frame(now) {
    const dtReal = Math.min(0.1, (now - last) / 1000);
    last = now;
    if (P.playing) {
      const i = sceneAt(P.t);
      const sc = V.scenes[i];
      const b = makeBeatHelper(sc, P.t - sc.T0);
      if (P.voice) {
        // hold the clock at the end of a beat while the utterance is still going
        const beat = sc.beats[b.cur];
        if (beat && P.t - sc.T0 >= beat.t1 - 0.05 && P.utt && synth.speaking) held = true;
        else held = false;
      } else held = false;
      if (!held) P.t += dtReal * P.speed;
      if (P.t >= V.T - 0.001) { P.t = V.T - 0.001; setPlaying(false); }
      const i2 = sceneAt(P.t); const sc2 = V.scenes[i2]; const b2 = makeBeatHelper(sc2, P.t - sc2.T0);
      maybeSpeak(sc2, b2);
      invalidate();
    }
    if (P.dirty) { P.dirty = false; render(); }
    requestAnimationFrame(frame);
  }

  // ---------------------------------------------------------------------- chrome wiring
  function buildMenu() {
    const list = document.getElementById('chapter-list'); list.innerHTML = '';
    V.chapters.forEach((ch, idx) => {
      if (ch.part) { const h = document.createElement('div'); h.className = 'part'; h.textContent = ch.part; list.appendChild(h); }
      const b = document.createElement('button'); b.className = 'chap'; b.dataset.ch = ch.id;
      const m = Math.floor(ch.T0 / 60), s = Math.floor(ch.T0 % 60);
      b.innerHTML = `<em>${idx + 1}</em><b>${ch.title}</b><span>${m}:${String(s).padStart(2, '0')}</span>`;
      b.onclick = () => { V.seek(ch.T0 + 0.01); try { history.replaceState(null, '', '#ch=' + ch.id); } catch (e) {} togglePanel('chapter-panel', false); };
      list.appendChild(b);
    });
    const ticks = document.getElementById('track-ticks'); ticks.innerHTML = '';
    V.chapters.forEach((ch) => { if (ch.T0 > 0) { const i = document.createElement('i'); i.style.left = (ch.T0 / V.T * 100) + '%'; ticks.appendChild(i); } });
  }
  function togglePanel(id, force) {
    const el = document.getElementById(id);
    const show = force === undefined ? el.hidden : force;
    ['chapter-panel', 'help-panel'].forEach((x) => { document.getElementById(x).hidden = true; });
    el.hidden = !show;
    document.getElementById('menu').setAttribute('aria-expanded', !document.getElementById('chapter-panel').hidden ? 'true' : 'false');
  }
  function fmtTip(t) { const m = Math.floor(t / 60), s = Math.floor(t % 60); return m + ':' + String(s).padStart(2, '0'); }
  function wireTrack() {
    const tr = document.getElementById('track'), tip = document.getElementById('track-tip');
    const seekFromEvent = (e) => {
      const r = tr.getBoundingClientRect();
      const u = clamp((e.clientX - r.left) / r.width);
      V.seek(u * V.T, true);
      return u;
    };
    const showTip = (e) => {
      const r = tr.getBoundingClientRect();
      const u = clamp((e.clientX - r.left) / r.width);
      const t = u * V.T; const ch = V.scenes[sceneAt(t)].ch;
      tip.textContent = fmtTip(t) + '  ' + ch.title; tip.style.left = (u * 100) + '%';
    };
    let drag = false;
    tr.addEventListener('pointerdown', (e) => { drag = true; tr.setPointerCapture(e.pointerId); tr.classList.add('active'); seekFromEvent(e); showTip(e); });
    tr.addEventListener('pointermove', (e) => { showTip(e); if (drag) seekFromEvent(e); });
    tr.addEventListener('pointerup', () => { drag = false; tr.classList.remove('active'); });
    tr.addEventListener('keydown', (e) => {
      if (e.key === 'ArrowLeft') { V.seek(P.t - 5, true); e.preventDefault(); }
      if (e.key === 'ArrowRight') { V.seek(P.t + 5, true); e.preventDefault(); }
    });
  }
  function setTheme(mode) { if (mode) document.documentElement.dataset.theme = mode; else delete document.documentElement.dataset.theme; readTheme(); invalidate(); }
  function setSpeed(s) { P.speed = s; document.getElementById('speed').value = String(s); if (P.utt) { cancelSpeech(); P.spokenBeat = null; } }
  function toggleFull() { const el = document.documentElement; if (document.fullscreenElement) document.exitFullscreen(); else el.requestFullscreen && el.requestFullscreen(); }

  function go(ch) { V.seek(ch.T0 + 0.01); }
  function jumpChapter(dir) {
    const i = V.chapters.indexOf(V.scenes[sceneAt(P.t)].ch);
    const j = clamp(i + dir, 0, V.chapters.length - 1);
    if (dir < 0 && P.t - V.chapters[i].T0 > 3 && dir === -1) { go(V.chapters[i]); return; }
    go(V.chapters[j]);
  }
  function wireKeys() {
    window.addEventListener('keydown', (e) => {
      const tag = (e.target.tagName || '').toLowerCase();
      if (tag === 'input' || tag === 'select' || tag === 'textarea') return;
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      const k2 = e.key;
      let done = true;
      if (k2 === ' ' || k2 === 'k' || k2 === 'K') setPlaying(!P.playing);
      else if (k2 === 'ArrowLeft') V.seek(P.t - 5, true);
      else if (k2 === 'ArrowRight') V.seek(P.t + 5, true);
      else if (k2 === 'j' || k2 === 'J') V.seek(P.t - 10, true);
      else if (k2 === 'l' || k2 === 'L') V.seek(P.t + 10, true);
      else if (k2 === 'n' || k2 === 'N') jumpChapter(1);
      else if (k2 === 'p' || k2 === 'P') jumpChapter(-1);
      else if (k2 === ',') { pauseIfPlaying(); V.seek(P.t - 1 / 30); }
      else if (k2 === '.') { pauseIfPlaying(); V.seek(P.t + 1 / 30); }
      else if (k2 === 'Home') V.seek(0, true);
      else if (k2 === 'End') V.seek(V.T - 0.5, true);
      else if (k2 >= '0' && k2 <= '9') V.seek((+k2) / 10 * V.T, true);
      else if (k2 === 'm' || k2 === 'M') toggleVoice();
      else if (k2 === 'c' || k2 === 'C') togglePanel('chapter-panel');
      else if (k2 === 't' || k2 === 'T') setTheme(C.dark ? 'light' : 'dark');
      else if (k2 === 'f' || k2 === 'F') toggleFull();
      else if (k2 === '?') togglePanel('help-panel');
      else if (k2 === 'Escape') { togglePanel('help-panel', false); togglePanel('chapter-panel', false); }
      else if (k2 === '+' || k2 === '=') stepSpeed(1);
      else if (k2 === '-' || k2 === '_') stepSpeed(-1);
      else done = false;
      if (done) e.preventDefault();
    });
  }
  const speeds = [0.75, 1, 1.25, 1.5, 2];
  function stepSpeed(d) { const i = speeds.indexOf(P.speed); setSpeed(speeds[clamp(i + d, 0, speeds.length - 1)]); }

  function parseHash() {
    const h = decodeURIComponent(location.hash.slice(1));
    if (!h) return false;
    const params = new URLSearchParams(h);
    if (params.has('ch')) { const ch = V.chapters.find((c2) => c2.id === params.get('ch')); if (ch) { V.seek(ch.T0 + 0.01); return true; } }
    if (params.has('t')) { V.seek(parseFloat(params.get('t')) || 0); return true; }
    return false;
  }

  V.start = function () {
    window.__errors = window.__errors || [];
    window.addEventListener('error', (e) => { window.__errors.push(String(e.message)); });
    const origErr = console.error.bind(console);
    console.error = (...a) => { window.__errors.push(a.map(String).join(' ')); origErr(...a); };

    cv = document.getElementById('cv'); ctx = cv.getContext('2d'); tx = document.getElementById('tx');
    readTheme(); layout(); buildMenu(); wireTrack(); wireKeys();
    new ResizeObserver(resize).observe(document.getElementById('stage-wrap'));
    window.addEventListener('resize', resize);
    resize();
    if (window.matchMedia) matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => { if (!document.documentElement.dataset.theme) { readTheme(); invalidate(); } });

    document.getElementById('pp').onclick = () => setPlaying(!P.playing);
    document.getElementById('big-play').onclick = () => setPlaying(true);
    document.getElementById('menu').onclick = () => togglePanel('chapter-panel');
    document.getElementById('help').onclick = () => togglePanel('help-panel');
    document.getElementById('theme').onclick = () => setTheme(C.dark ? 'light' : 'dark');
    document.getElementById('fs').onclick = toggleFull;
    document.getElementById('voice').onclick = toggleVoice;
    document.getElementById('speed').onchange = (e) => setSpeed(parseFloat(e.target.value));
    cv.addEventListener('click', (e) => {
      if (curScene && curScene.onClick) {
        const [x, y] = toStage(e.clientX, e.clientY);
        const handled = curScene.onClick(x, y, curScene.ix || (curScene.ix = curScene.init ? curScene.init() : {}));
        if (handled !== false) { pauseIfPlaying(); invalidate(); return; }
      }
      setPlaying(!P.playing);
    });
    document.addEventListener('click', (e) => {
      const panel = document.getElementById('chapter-panel');
      if (!panel.hidden && !panel.contains(e.target) && e.target.id !== 'menu') togglePanel('chapter-panel', false);
    });

    // test and deep-link hooks: ?t=seconds, ?ch=id, ?theme=dark|light; hash also works for chapters.
    const q = new URLSearchParams(location.search);
    if (q.get('theme')) setTheme(q.get('theme'));
    if (q.has('rm')) V.RM = q.get('rm') !== '0';
    let linked = parseHash();
    if (q.has('t')) { V.seek(parseFloat(q.get('t'))); linked = true; }
    if (q.has('ch')) { const ch = V.chapters.find((c2) => c2.id === q.get('ch')); if (ch) { V.seek(ch.T0 + 0.01); linked = true; } }
    window.addEventListener('hashchange', () => { parseHash(); });
    render();
    requestAnimationFrame((n) => { last = n; requestAnimationFrame(frame); });
    if (q.get('play') === '1') setPlaying(true);
    if (q.get('shot')) { P.everPlayed = true; document.getElementById('big-play').hidden = true; }
    V.ready = true;
  };
  window.__seek = (t) => { V.seek(t); render(); return V.T; };
  window.__state = () => ({ T: V.T, t: P.t, scenes: V.scenes.length, chapters: V.chapters.map((c2) => [c2.id, c2.T0, c2.T1, c2.title]), errors: window.__errors });
})();
