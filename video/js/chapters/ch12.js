/* Chapter 12: the first rectangle (real Hoffman--Singleton data). */
(function () {
  const { C, c, lerp } = V; const D = window.Dr; const DATA = window.DATA;
  V.chapter('rectangle', 'The first rectangle');
  const HS = DATA.hs;

  V.scene({
    beats: [
      'Now the symmetry-breaking step, where Babai and the new paper part ways. Aggregation either finds useful symmetry, or it hands us a coherent configuration: a colouring of the pairs of labels, stable under refinement, on a set C containing a fixed fraction of the labels.',
      'To make this concrete: a real example. Take the Hoffman–Singleton graph: 50 vertices, each with 7 neighbours. Two adjacent vertices have no common neighbour. Two non-adjacent ones have exactly one. Think of its vertices as our labels, and edges and non-edges as the colours on pairs.',
      'Individualize one vertex, and branch over where it could go in the other instance. Classify every other vertex by its relation to the chosen one. Its neighbours are one class of 7. Its non-neighbours are one class of 42.',
      'The largest class has 42 out of 50 vertices, more than three quarters: a dominant class, called W.',
      'Choose a second class, R: here, the 7 neighbours. Look at the bipartite graph between W and R, rows W, columns R. I computed this for this graph: every row has exactly one entry, every column exactly six.',
      'That is the first rectangle. Both sides are real subsets of the original labels; no new objects were introduced. And that is where this algorithm stops: it solves the rectangle, and uses that answer.',
    ],
    draw(c_, b) {
      D.title('Individualize, and the classes fall out', { alpha: b.on(0) });
      const R = 240, cx0 = 280, cy0 = 380;
      const a0 = b.on(1);
      // HS drawn schematically: 50 points on a circle, one individualized.
      const pts = D.circle(50, cx0, cy0, R);
      const ind = b.t > b.s(2) + 0.5;
      const nbr = (i) => i >= 1 && i <= 7; // schematic ordering for display of class sizes
      pts.forEach((p, i) => {
        const col = !ind ? C.bg3 : i === 0 ? C.lab : nbr(i) ? C.aqua : C.blue;
        c.circle(p[0], p[1], ind && i === 0 ? 11 : 6.5, { fill: col, alpha: a0 });
      });
      D.simplified(280, 680, a0 * 0.95, 'drawn schematically: real graph, not its real layout');
      c.text('50 labels, 7 neighbours each', cx0, cy0 - 18, { size: 19, fill: C.ink2, alpha: a0 });
      c.text('adjacent: 0 common · non-adjacent: 1 common', cx0, cy0 + 14, { size: 16, fill: C.ink2, alpha: a0 });
      const a2 = b.on(2);
      if (ind) {
        c.text('one source label', 280, 95, { size: 20, fill: C.ink, alpha: a2 });
      }
      // Right side: the rectangle matrix 42x7
      const M = HS.matrix;
      const x0 = 760, y0 = 112, cw = 42, ch = 12;
      const a4 = b.on(4);
      if (a4 > 0) {
        for (let j = 0; j < 42; j++) for (let i = 0; i < 7; i++) {
          const on = M[j][i];
          c.rect(x0 + i * cw, y0 + j * ch, cw - 2, ch - 1, { fill: on ? C.blue : C.bg3, r: 1, alpha: a4 });
        }
        for (let t = 0; t <= 7; t++) c.line(x0, y0 + t * 6 * ch, x0 + 7 * cw - 2, y0 + t * 6 * ch, { stroke: C.bg, lw: 2, alpha: a4 });
        c.text('R (7 columns)', x0 + 3.5 * cw, y0 - 22, { size: 19, alpha: a4 });
        c.text('W', x0 - 30, y0 + 21 * ch, { size: 22, weight: 600, alpha: a4 });
        c.text('42', x0 - 30, y0 + 21 * ch + 26, { size: 18, fill: C.ink2, alpha: a4 });
        c.text('each row: 1 entry · each column: 6', x0 + 3.5 * cw, y0 + 42 * ch + 34, { size: 18, fill: C.ink2, alpha: a4 });
      }
      const a3 = b.on(3);
      if (b.t < b.s(4) + 0.2) {
        c.text('dominant class W', 900, 200, { size: 26, weight: 650, alpha: a3 });
        c.tex('|W|=42,\\ |R|=7', 900, 245, { size: 26, alpha: a3 });
      }
      c.tex('|W|>\\eta|C|,\\ |R|\\le|C|-|W|', 620, 640, { size: 19, alpha: b.on(5) });
    },
  });

  V.scene({
    beats: [
      'Why would solving that one rectangle lower a cap on the entire giant? This is the prettiest argument in the paper, so let us look at it carefully.',
      'Solve the rectangle: find every permitted automorphism of this bipartite graph. Suppose an automorphism fixes every column. Then it can only permute rows with identical patterns. In this example, the twin classes have size 6.',
      'In general, after complementing the graph if needed, every column has at most w over 2 ones, and a twin class is contained in one column\'s rows. So every twin class has size at most w over 2.',
      'And what about an automorphism that moves the columns? It acts on the smaller side, R. So every large alternating section of the left action has to come from a twin class, of size at most w over 2, or from the right side, of size at most r. Its alternating width is at most the larger of w over 2 and r.',
      'Extend that answer by arbitrary permutations of everything outside W, with the right parity. Now we have a group, an overcoset, containing every parent isomorphism in this branch, and its alternating width on all of Gamma is at most the larger of w over 2, r, and q minus w.',
      'For the real numbers here, w equals 42, r is 7, q is 50. So the width is at most max of 21, 7, and 8, which is 21. And in general: a fixed fraction beta of q, less than 1. The cap on that level has fallen from at least q, to beta q.',
      'Babai, at this point, keeps going, recursing inside the rectangle through more individualizations, at a cost of m to the log m. The new paper simply stops. It takes the first rectangle, solves it exactly, and uses only the bound on the alternating width it provides.',
    ],
    draw(c_, b) {
      D.title('Why one rectangle lowers a cap', { alpha: b.on(0) });
      const a = b.on(1);
      // rectangle with twin classes shaded
      const x0 = 110, y0 = 110, cw = 40, ch = 12;
      const M = HS.matrix;
      for (let j = 0; j < 42; j++) for (let i = 0; i < 7; i++) {
        const on = M[j][i]; const cls = Math.floor(j / 6);
        const baseCol = cls % 2 ? C.aqua : C.violet;
        c.rect(x0 + i * cw, y0 + j * ch, cw - 2, ch - 1, { fill: on ? C.blue : baseCol, r: 1, alpha: a * (on ? 1 : 0.16) });
      }
      for (let t = 0; t <= 7; t++) c.line(x0, y0 + t * 6 * ch, x0 + 7 * cw - 2, y0 + t * 6 * ch, { stroke: C.bg, lw: 2, alpha: a });
      for (let cls = 0; cls < 7; cls++) c.text(String(6), x0 - 22, y0 + (cls + 0.5) * 6 * ch, { size: 17, fill: C.ink2, alpha: a });
      c.text('twin classes: size 6', x0 + 3.5 * cw, y0 + 42 * ch + 24, { size: 18, fill: C.ink2, alpha: a });
      // proof steps right
      const steps = [
        { y: 130, on: 1, tex: '\\text{fixes all columns}\\Rightarrow\\text{permutes twin classes only}' },
        { y: 200, on: 2, tex: '\\text{twin class}\\ \\le\\ w/2' },
        { y: 270, on: 3, tex: '\\text{left action: width}\\le\\max\\{w/2,\\ r\\}' },
        { y: 340, on: 4, tex: '\\text{extended: width}\\le\\max\\{w/2,\\ r,\\ q-w\\}' },
      ];
      steps.forEach((s) => { const al = b.on(s.on); c.tex(s.tex, 760, s.y, { size: 24, alpha: al }); });
      const a5 = b.on(5);
      c.rect(530, 400, 660, 130, { fill: C.bg2, stroke: C.Q, lw: 2.5, r: 10, alpha: a5 });
      c.tex('\\max\\{21,\\ 7,\\ 8\\}=21', 860, 442, { size: 28, alpha: a5 });
      c.tex('\\text{cap} \\ \\ q\\ \\longrightarrow\\ \\beta q', 860, 492, { size: 26, fill: C.ink, alpha: a5 });
      c.text('real numbers for this rectangle', 560, 415, { size: 16, fill: C.ink2, align: 'left', alpha: a5 });
      const a6 = b.on(6);
      c.text('Babai keeps recursing here. HJ stop here.', 800, 610, { size: 28, weight: 650, alpha: a6 });
      c.tex('m^{O(\\log m)}\\ \\text{ versus }\\ q^{O(1)}', 800, 660, { size: 24, alpha: a6, fill: C.ink2 });
    },
  });
})();
