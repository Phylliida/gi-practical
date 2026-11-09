/* Chapter 3: the parity trap (CFI over K4). */
(function () {
  const { C, c } = V; const D = window.Dr; const DATA = window.DATA;
  V.chapter('cfi', 'The parity trap');

  // One gadget: three edge-ends, each a pair (0,1)\\, middle vertices = even subsets.
  const gadPos = (cx, cy, R) => {
    const ends = [0, 1, 2].map((i) => {
      const a = -Math.PI / 2 + i * 2 * Math.PI / 3;
      const out = [cx + R * Math.cos(a), cy + R * Math.sin(a)];
      const perp = [-Math.sin(a), Math.cos(a)];
      return { p0: [out[0] + 22 * perp[0], out[1] + 22 * perp[1]], p1: [out[0] - 22 * perp[0], out[1] - 22 * perp[1]] };
    });
    const mids = [[-44, -18], [44, -18], [-16, 42], [34, 44]].map((d) => [cx + d[0], cy + d[1]]);
    return { ends, mids };
  };
  const evenSets = [[0, 0, 0], [1, 1, 0], [1, 0, 1], [0, 1, 1]];
  V.scene({
    beats: [
      'Take a vertex with three edges coming out of it. Replace each edge end with a pair of small dots, a zero side and a one side.',
      'In the middle, add one vertex for each way of choosing an even number of the three edges to put on their one side. There are four of those.',
      'Connect each middle vertex to the sides it picks.',
      'Now notice what this gadget can do. Flip two of the three edge pairs, and shuffle the middle vertices. Nothing changes.',
      'Flip just one edge pair, and there is no way to fix it. The gadget stores a parity.',
    ],
    draw(c_, b) {
      D.title('A gadget that stores a parity', { alpha: b.on(0) });
      const g = gadPos(640, 400, 220);
      const u = b.p(3, 0.1, 0.8);
      const flip = (idx, k) => ((b.in(3) && u > 0.5 && (k === 0 || k === 1)) ? 1 - idx : idx);
      const col = [C.blue, C.orange, C.aqua];
      const al = b.on(0);
      g.ends.forEach((e, k) => {
        c.circle(e.p0[0], e.p0[1], 15, { fill: col[k], alpha: al }); c.circle(e.p1[0], e.p1[1], 15, { fill: col[k], alpha: al });
        c.text('0', e.p0[0], e.p0[1] + 0.5, { size: 15, weight: 700, fill: '#111', alpha: al }); c.text('1', e.p1[0], e.p1[1] + 0.5, { size: 15, weight: 700, fill: '#111', alpha: al });
      });
      const mAl = b.on(1);
      const sel = (mi) => evenSets[mi];
      evenSets.forEach((S, mi) => {
        const eAl = b.p(2, 0.05 + mi * 0.2, 0.4 + mi * 0.2);
        g.ends.forEach((e, k) => {
          const end = S[k] ? e.p1 : e.p0;
          c.line(g.mids[mi][0], g.mids[mi][1], end[0], end[1], { stroke: C.ink3, lw: 1.8, alpha: eAl });
        });
        c.circle(g.mids[mi][0], g.mids[mi][1], 16, { fill: C.bg3, stroke: C.ink2, alpha: mAl });
        c.text(S.join(''), g.mids[mi][0], g.mids[mi][1] + 0.5, { size: 12, alpha: mAl, weight: 600 });
      });
      // Flip animation
      if (b.in(3, 4)) {
        const pa = b.p(3, 0.1, 0.8);
        [0, 1].forEach((k) => {
          const e = g.ends[k]; const m = [(e.p0[0] + e.p1[0]) / 2, (e.p0[1] + e.p1[1]) / 2];
          c.arrow(m[0] - 34, m[1], m[0] + 34, m[1], { stroke: C.mag, lw: 3, alpha: pa > 0 ? 1 : 0 });
        });
        c.text('flip two: a symmetry', 640, 86, { size: 24, fill: C.ink, weight: 600, alpha: 1 });
      }
      if (b.in(4)) c.text('flip one: impossible', 640, 86, { size: 24, weight: 600, alpha: b.on(4) });
    },
  });

  // Full K4 CFI layout, two copies.
  const base = DATA.cfi.base_edges;
  const G0 = DATA.cfi;
  function layout(cx, cy, R) {
    const corners = [[cx - R, cy - R], [cx + R, cy - R], [cx + R, cy + R], [cx - R, cy + R]];
    return corners;
  }
  function cfiDraw(cornerPos, twist, o = {}) {
    // draw gadget centres, wires between gadgets\\, twist = index of the twisted base edge.
    const a = o.alpha ?? 1;
    const cols = C;
    base.forEach(([u, v], idx) => {
      const A = cornerPos[u], B = cornerPos[v];
      const dx = B[0] - A[0], dy = B[1] - A[1];
      const L = Math.hypot(dx, dy); const px = -dy / L, py = dx / L;
      const off = 7;
      const shrink = (x, y, f) => [x + dx * f, y + dy * f];
      const a0 = shrink(A[0] + px * off, A[1] + py * off, 0.14), a1 = shrink(A[0] - px * off, A[1] - py * off, 0.14);
      const b0 = shrink(B[0] + px * off, B[1] + py * off, -0.14), b1 = shrink(B[0] - px * off, B[1] - py * off, -0.14);
      const isTw = idx === twist;
      c.line(a0[0], a0[1], isTw ? b1[0] : b0[0], isTw ? b1[1] : b0[1], { stroke: isTw ? C.red : C.ink3, lw: isTw ? 2.6 : 1.4, alpha: a });
      c.line(a1[0], a1[1], isTw ? b0[0] : b1[0], isTw ? b0[1] : b1[1], { stroke: isTw ? C.red : C.ink3, lw: isTw ? 2.6 : 1.4, alpha: a });
      [a0, a1, b0, b1].forEach((p) => c.circle(p[0], p[1], 3.2, { fill: C.ink2, alpha: a }));
    });
    cornerPos.forEach((p) => {
      for (let i = 0; i < 4; i++) { const ang = i * Math.PI / 2 + Math.PI / 4; c.circle(p[0] + 15 * Math.cos(ang), p[1] + 15 * Math.sin(ang), 5, { fill: C.bg3, stroke: C.ink2, lw: 1.6, alpha: a }); }
    });
  }

  V.scene({
    init: () => ({ twist: 0, touched: false }),
    onClick(x, y, ix) {
      const R = 150; const pos = layout(960, 365, R);
      let best = -1, bd = 1e9;
      base.forEach(([u, v], i) => {
        const mx = (pos[u][0] + pos[v][0]) / 2, my = (pos[u][1] + pos[v][1]) / 2;
        const d = Math.hypot(mx - x, my - y); if (d < bd) { bd = d; best = i; }
      });
      if (bd > 70) return false;
      const [a, b] = base[ix.twist];
      if (best !== ix.twist && (base[best].includes(a) || base[best].includes(b))) { ix.twist = best; ix.touched = true; }
      return true;
    },
    beats: [
      'Now put one gadget on every corner of a base graph. Here the base is the complete graph on four corners, and wires join the matching sides along each edge. That makes 40 vertices.',
      'Make a second copy, and cross one pair of wires. Just one.',
      'Every vertex still has degree three. Every small neighbourhood of every vertex looks the same in both copies. I ran the real computation on these 40-vertex graphs: colour refinement gives one colour on both.',
      'Even two-dimensional refinement, on all ordered pairs, gives identical answers. And yet the two graphs are genuinely not isomorphic. That has also been checked.',
      { say: 'Here is why. Because you can flip two edges at a gadget, a crossing can slide to a neighbouring edge. Try it: click an edge next to the red one. The crossing moves, but it never disappears.', hold: 2.5 },
      'So the only thing distinguishing the two graphs is the parity of the crossings: one global bit, spread over the whole graph.',
      'Babai likes to say the job is to close the gap between symmetry and regularity. Refinement finds regularity. These graphs are perfectly regular and have no such symmetry. To tell the difference, we need to reason about symmetry directly. That means group theory.',
    ],
    draw(c_, b, ix) {
      D.title('Two copies of the same local picture', { alpha: b.on(0) });
      const R = 150;
      const pos0 = layout(320, 365, R), pos1 = layout(960, 365, R);
      cfiDraw(pos0, -1, { alpha: b.on(0) });
      c.text('untwisted', 320, 560, { size: 22, alpha: b.on(0) });
      const a1 = b.on(1);
      cfiDraw(pos1, ix.twist, { alpha: a1 });
      c.text('one pair of wires crossed', 960, 560, { size: 22, alpha: a1 });
      // Results
      const a = b.on(2);
      c.rect(80, 600, 1120, 68, { fill: C.bg2, stroke: C.rule, r: 9, alpha: Math.max(a, 0), lw: 1 });
      if (b.in(2, 3)) c.text('colour refinement: 40 vertices, one colour, on both graphs', 640, 634, { size: 21, weight: 500, alpha: b.on(2, 3) });
      if (b.in(3, 4)) c.text('2-dimensional refinement: identical on both  ·  yet not isomorphic', 640, 634, { size: 21, weight: 500, alpha: b.on(3, 4) });
      if (b.in(4, 5)) D.tryIt(640, 634, b.on(4, 5), 'Try it: click an edge beside the red one');
      if (b.in(5, 6)) c.text('only the parity of crossings differs: one global bit', 640, 634, { size: 22, weight: 600, alpha: b.on(5, 6) });
      if (b.in(6)) c.text('symmetry vs regularity', 640, 634, { size: 24, weight: 600, alpha: b.on(6) });
    },
  });
})();
