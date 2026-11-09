/* Shared drawing vocabulary for the chapters. Everything is immediate-mode and pure in its arguments. */
(function () {
  'use strict';
  const D = (window.Dr = {});
  const C = V.C, c = V.c;
  const { lerp, ease } = V;
  D.lerp = lerp; D.ease = ease;

  D.circle = (n, cx, cy, r, rot = -Math.PI / 2) => {
    const out = [];
    for (let i = 0; i < n; i++) { const a = rot + (2 * Math.PI * i) / n; out.push([cx + r * Math.cos(a), cy + r * Math.sin(a)]); }
    return out;
  };

  // A graph drawing. pos: list of [x,y]; edges: pairs; opts: nodeR, nodeFill(i) or colour, edgeStroke, edgeAlpha(i,e), labels, ...
  D.graph = (pos, edges, o = {}) => {
    const r = o.r || 13;
    const eAlpha = o.edgeAlpha || (() => 1);
    edges.forEach(([a, b], i) => {
      const al = (typeof eAlpha === 'function' ? eAlpha(i, a, b) : eAlpha) * (o.alpha ?? 1);
      if (al <= 0) return;
      c.line(pos[a][0], pos[a][1], pos[b][0], pos[b][1], { stroke: o.edgeStroke || C.ink3, lw: o.lw || 2.2, alpha: al });
    });
    pos.forEach((p, i) => {
      const fill = typeof o.fill === 'function' ? o.fill(i) : (o.fill || C.bg);
      const al = (typeof o.nodeAlpha === 'function' ? o.nodeAlpha(i) : (o.nodeAlpha ?? 1)) * (o.alpha ?? 1);
      if (al <= 0) return;
      c.circle(p[0], p[1], r, { fill: C.bg, alpha: al });
      c.circle(p[0], p[1], r, { fill, stroke: o.stroke || C.ink2, lw: o.nodeLw || 2, alpha: al });
      if (o.labels) {
        const lab = typeof o.labels === 'function' ? o.labels(i) : o.labels[i];
        if (lab != null) c.text(String(lab), p[0], p[1] + 0.5, { size: o.labelSize || Math.round(r * 1.05), fill: o.labelFill || C.ink, alpha: al, weight: 600 });
      }
    });
  };

  // Standard Petersen drawing: outer pentagon, inner star.
  D.petersenPos = (cx, cy, R) => {
    const pts = [];
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (2 * Math.PI * i) / 5; pts.push([cx + R * Math.cos(a), cy + R * Math.sin(a)]); }
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (2 * Math.PI * i) / 5; pts.push([cx + R * 0.48 * Math.cos(a), cy + R * 0.48 * Math.sin(a)]); }
    return pts;
  };
  D.prismPos = (cx, cy, R) => {
    const pts = [];
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (2 * Math.PI * i) / 5; pts.push([cx + R * Math.cos(a), cy + R * Math.sin(a)]); }
    for (let i = 0; i < 5; i++) { const a = -Math.PI / 2 + (2 * Math.PI * i) / 5; pts.push([cx + R * 0.52 * Math.cos(a), cy + R * 0.52 * Math.sin(a)]); }
    return pts;
  };

  D.title = (s, o = {}) => { c.text(s, V.W / 2, o.y ?? 46, { size: o.size || 30, weight: 600, fill: C.ink, alpha: o.alpha ?? 1 }); };
  D.sub = (s, y, o = {}) => { c.text(s, V.W / 2, y, { size: o.size || 22, fill: o.fill || C.ink2, alpha: o.alpha ?? 1 }); };

  // A small "simplified" chip, placed where it applies.
  D.chip = (txt, x, y, o = {}) => {
    const size = o.size || 15;
    const w = c.width(txt, { size }) + 20;
    c.rect(x - w / 2, y - 14, w, 28, { fill: o.fill || C.chip, stroke: o.stroke || C.rule, lw: 1.2, r: 7, alpha: o.alpha ?? 1 });
    c.text(txt, x, y + 0.5, { size, fill: o.textFill || C.ink2, alpha: o.alpha ?? 1 });
  };
  D.simplified = (x, y, alpha = 1, txt = 'simplified') => D.chip(txt, x, y, { alpha, stroke: C.orange, textFill: C.ink });
  D.tryIt = (x, y, alpha = 1, txt = 'Try it') => D.chip(txt, x, y, { alpha, stroke: C.blue, textFill: C.ink, size: 16 });

  // panel: rounded card
  D.card = (x, y, w, h, o = {}) => c.rect(x, y, w, h, { fill: o.fill || C.bg2, stroke: o.stroke || C.rule, lw: o.lw || 1.2, r: o.r || 12, alpha: o.alpha ?? 1 });

  // A cost/size bar drawn from baseline with a label
  D.bar = (x, y, w, h, fill, o = {}) => c.rect(x, y - h, w, Math.max(h, 0), { fill, r: 3, alpha: o.alpha ?? 1 });

  // A grid of cells, cell colour function fn(i,j) -> colour or null
  D.grid = (x, y, cols, rows, cell, fn, o = {}) => {
    const gap = o.gap ?? 2;
    for (let j = 0; j < rows; j++) for (let i = 0; i < cols; i++) {
      const col = fn(i, j); if (col == null) continue;
      c.rect(x + i * cell, y + j * cell, cell - gap, cell - gap, { fill: col, r: o.r ?? 2, alpha: o.alpha ?? 1 });
    }
  };

  // "The bill": three log tiles, top right. state: array of up to 3 of {label, color, alpha, strike}
  D.bill = (cx, y, tiles, o = {}) => {
    const w = o.w || 86, h = o.h || 42, gap = o.gap || 12, size = o.size || 19;
    const n = tiles.length;
    const totalW = n * w + (n - 1) * (gap + 18);
    let x = cx - totalW / 2;
    tiles.forEach((tile, i) => {
      const al = (tile.alpha ?? 1) * (o.alpha ?? 1);
      if (i > 0) c.text('×', x - 15, y, { size: 22, fill: C.ink3, alpha: al });
      c.rect(x, y - h / 2, w, h, { fill: tile.fill || C.bg2, stroke: tile.color || C.rule, lw: 2, r: 8, alpha: al });
      c.tex(tile.tex || '\\log n', x + w / 2, y, { size, fill: tile.textFill || C.ink, alpha: al, key: 'bill' + i });
      if (tile.strike) c.line(x + 6, y + h / 2 - 6, x + w - 6, y - h / 2 + 6, { stroke: C.red, lw: 3, alpha: al * tile.strike });
      x += w + gap + 18;
    });
  };

  // Term-coloured potential formula: Φ = A(x² + ρx + σx + Q) + Bh, with highlight on one term (0..4).
  D.potential = (cx, y, active, o = {}) => {
    const size = o.size || 30;
    const parts = [
      { t: '\\Phi = A(', col: C.ink },
      { t: 'x^2', col: C.x2, id: 0 },
      { t: '+', col: C.ink },
      { t: '\\rho x', col: C.rho, id: 1 },
      { t: '+', col: C.ink },
      { t: '\\sigma x', col: C.sig, id: 2 },
      { t: '+', col: C.ink },
      { t: 'Q', col: C.Q, id: 3 },
      { t: ')+', col: C.ink },
      { t: 'Bh', col: C.h, id: 4 },
    ];
    const widths = [86, 44, 30, 44, 30, 44, 30, 28, 40, 44].map((w) => (w * size) / 30);
    let x = cx - widths.reduce((a, b) => a + b, 0) / 2;
    parts.forEach((p, i) => {
      const lit = p.id != null && (active === true || (Array.isArray(active) ? active.includes(p.id) : active === p.id));
      const al = (o.alpha ?? 1) * (p.id != null && active != null && active !== true && !lit ? 0.32 : 1);
      if (lit) c.rect(x - 4, y - size * 0.8, widths[i] + 8, size * 1.6, { fill: p.col, alpha: (o.alpha ?? 1) * 0.16, r: 6 });
      c.tex(p.t, x + widths[i] / 2, y, { size, fill: p.col, alpha: al, key: 'pot' + i });
      x += widths[i];
    });
  };
  // Resource colours in a list for bars etc.
  D.termColor = (i) => [C.x2, C.rho, C.sig, C.Q, C.h][i];

  // Small wrapped caption text inside the picture (kept rare by the redundancy rule).
  D.note = (s, x, y, o = {}) => c.text(s, x, y, { size: o.size || 19, fill: o.fill || C.ink2, align: o.align || 'left', alpha: o.alpha ?? 1, italic: o.italic });

  // simple labelled box for flowcharts
  D.box = (x, y, w, h, label, o = {}) => {
    const a = o.alpha ?? 1;
    c.rect(x - w / 2, y - h / 2, w, h, { fill: o.fill || C.bg2, stroke: o.stroke || C.rule, lw: o.lw || 1.5, r: 9, alpha: a });
    if (o.tex) c.tex(label, x, y, { size: o.size || 20, alpha: a, fill: o.textFill || C.ink });
    else c.text(label, x, y + 0.5, { size: o.size || 18, alpha: a, fill: o.textFill || C.ink, weight: o.weight || 500 });
  };

  D.arrowBetween = (x1, y1, x2, y2, o = {}) => c.arrow(x1, y1, x2, y2, { stroke: o.stroke || C.ink3, lw: o.lw || 2, alpha: o.alpha ?? 1 });

  // Interpolate between two point sets
  D.lerpPts = (A, B, u) => A.map((p, i) => [lerp(p[0], B[i][0], u), lerp(p[1], B[i][1], u)]);

  // Line drawing of the "Part" banner shown at start of each part/chapter: chapter title card
  D.chapterCard = (b, title, sub, o = {}) => {
    const u = o.u !== undefined ? o.u : 1;
    c.text(title, V.W / 2, V.H / 2 - 18, { size: o.size || 44, weight: 650, fill: C.ink, alpha: u });
    if (sub) c.text(sub, V.W / 2, V.H / 2 + 34, { size: 24, fill: C.ink2, alpha: u });
  };
})();
