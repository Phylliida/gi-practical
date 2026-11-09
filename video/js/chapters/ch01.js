/* Chapter 1: the question. */
(function () {
  const { C, c } = V; const D = window.Dr; const DATA = window.DATA;
  const { lerp } = V;
  V.part('Part I: the problem');
  V.chapter('question', 'The question');

  const petE = DATA.petersen.edges, priE = DATA.prism.edges;
  const pP = D.petersenPos(330, 370, 200), pQ = D.prismPos(950, 370, 200);
  // an explicit four-cycle of the prism: outer i, i+1, inner i+1, inner i
  const c4 = [[0, 1], [1, 6], [6, 5], [5, 0]];

  V.scene({
    beats: [
      'Here are two networks. Ten dots each, fifteen lines, and every dot touches exactly three lines.',
      { say: 'Are they the same network, just drawn differently? Take a moment and guess.', hold: 1.5 },
      'Same means this: you can rename the dots of the left one so that its lines become exactly the lines of the right one.',
      'With ten dots, you could try all 3.6 million renamings. There is a quicker way. Count the four-sided loops.',
      'The left one has none. The right one has five. So they are different.',
    ],
    draw(c_, b) {
      D.title('Same graph or not?', { alpha: b.on(0) });
      const a = b.on(0);
      D.graph(pP, petE, { r: 13, fill: C.bg3, alpha: a });
      D.graph(pQ, priE, { r: 13, fill: C.bg3, alpha: a });
      c.text('10 dots · 15 lines · all degree 3', 330, 608, { size: 20, fill: C.ink2, alpha: a });
      c.text('10 dots · 15 lines · all degree 3', 950, 608, { size: 20, fill: C.ink2, alpha: a });
      // viewer thinking
      c.text('?', 640, 350, { size: 120, weight: 700, fill: C.ink3, alpha: b.on(1, 2) * 0.55 });
      // renaming sample
      const u = b.p(2, 0.1, 0.9);
      if (u > 0 && b.t < b.s(3) + 0.5) {
        const al = b.on(2, 3);
        const k = Math.floor(u * 4) % 4, f = D.ease(u * 4 - Math.floor(u * 4));
        const a2 = [0, 4, 6, 2];
        const src = pP[a2[k]], dst = pQ[a2[k] === 2 ? 7 : 3];
        c.arrow(src[0], src[1] - 16, lerp(src[0], dst[0], f), lerp(src[1], dst[1], f) - 22, { stroke: C.violet, lw: 2.5, alpha: al * Math.max(f, 0.3) });
      }
      // four-cycle highlight
      const h = b.on(3);
      if (h > 0) {
        c4.forEach(([x, y]) => c.line(pQ[x][0], pQ[x][1], pQ[y][0], pQ[y][1], { stroke: C.orange, lw: 6, alpha: h }));
        c.text('five 4-cycles', 950, 92, { size: 24, weight: 600, fill: C.ink, alpha: b.on(4) });
        c.text('no 4-cycles', 330, 92, { size: 24, weight: 600, fill: C.ink, alpha: b.on(4) });
      }
    },
  });

  // growth comparison: x = log10 n, y = log10(exponent of the bound)
  const fns = [
    { id: 'fact', tex: 'n!', f: (L) => (Math.pow(10, L) * L * Math.log(10)), col: () => C.red, labelL: 3.2 },
    { id: 'bkl', tex: '\\exp\\sqrt{n\\log n}', f: (L) => Math.sqrt(Math.pow(10, L) * L * Math.log(10)), col: () => C.orange, labelL: 3.7 },
    { id: 'bab', tex: '\\exp(\\log^3 n)', f: (L) => Math.pow(L * Math.log(10), 3), col: () => C.violet, labelL: 2.2 },
    { id: 'hj', tex: '\\exp(\\log^2 n)', f: (L) => Math.pow(L * Math.log(10), 2), col: () => C.aqua, labelL: 2.2 },
  ];
  V.scene({
    beats: [
      'We got lucky: a small pattern gave it away. The real question is whether some recipe always works, on every pair of graphs, in a time we can prove.',
      'The honest baseline is to try all n-factorial renamings.',
      'In 1983, Babai, Kantor and Luks brought that down to e to the square root of n log n, roughly.',
      'In 2015 Babai announced a quasi-polynomial algorithm. Helfgott\'s careful accounting of the corrected version gives e to the log cubed of n.',
      'And in November 2026, a preprint by Hajiaghayi and JafariRaviz gives a proof of e to the order log squared of n. That is the same as n to the order log n.',
      'This chart shows only the shape: the constants are ignored, so read nothing into where the lines cross.',
    ],
    draw(c_, b) {
      const X0 = 120, Y0 = 620, XW = 610, YH = 470;
      const a = b.on(0);
      D.title('The bounds, compressed', { alpha: a, y: 44 });
      // axes
      c.line(X0, Y0, X0 + XW, Y0, { stroke: C.rule, lw: 2, alpha: a });
      c.line(X0, Y0, X0, Y0 - YH, { stroke: C.rule, lw: 2, alpha: a });
      c.tex('n', X0 + XW + 22, Y0, { size: 22, fill: C.ink2, alpha: a });
      c.text('(log of the running time, log scale)', X0 + 14, Y0 - YH - 22, { size: 17, fill: C.ink2, align: 'left', alpha: a });
      for (const L of [2, 4, 6, 8, 10]) {
        const xx = X0 + ((L - 1) / 10) * XW;
        c.line(xx, Y0, xx, Y0 + 7, { stroke: C.rule, lw: 2, alpha: a });
        c.tex('10^{' + L + '}', xx, Y0 + 26, { size: 18, fill: C.ink2, alpha: a });
      }
      const ymax = Math.log10(1e10 * 10 * Math.log(10));
      const xs = (L) => X0 + ((L - 1) / 10) * XW;
      const ys = (v) => Y0 - (Math.log10(v) / ymax) * YH;
      const appear = [b.on(1), b.on(2), b.on(3), b.on(4)];
      fns.forEach((fn, i) => {
        const al = appear[i];
        if (al <= 0) return;
        const pts = [];
        for (let L = 1; L <= 11.001; L += 0.1) {
          const v = fn.f(L);
          const y = ys(v);
          if (y < Y0 - YH - 4 || y > Y0) continue;
          pts.push([xs(L), y]);
        }
        const prog = b.p(i + 1, 0, 0.8);
        const cnt = Math.max(2, Math.ceil(pts.length * prog));
        c.poly(pts.slice(0, cnt), { stroke: fn.col(), lw: 3.2, close: false, alpha: al });
        // direct label
        const end = pts[Math.min(cnt - 1, pts.length - 1)];
        c.tex(fn.tex, end[0] + 8, end[1] - 14, { size: 21, align: 'left', fill: fn.col(), alpha: prog > 0.9 ? al : 0 });
      });
      // right column: years
      const rows = [['brute force', '\\text{try all } n!', C.red], ['1983', 'e^{O(\\sqrt{n\\log n})}', C.orange], ['2015–17', 'e^{O((\\log n)^3)}', C.violet], ['Nov 2026 preprint', 'e^{O((\\log n)^2)}=n^{O(\\log n)}', C.aqua]];
      rows.forEach(([yr, tex, col], i) => {
        const al = appear[i], y = 170 + i * 92;
        c.circle(918, y, 7, { fill: col, alpha: al });
        c.text(yr, 935, y, { size: 21, align: 'left', fill: C.ink2, alpha: al });
        c.tex(tex, 935, y + 32, { size: 26, align: 'left', alpha: al, key: 'yr' + i });
      });
      D.simplified(1030, 570, b.on(5), 'shape only, constants ignored');
    },
  });

  V.scene({
    beats: [
      'Take the old bound and the new one, and write what is inside the exponent as a product.',
      'Log n, times log n, times log n. That was the bill for about a decade. The new one has two factors.',
      'So here is the question for the rest of this video. Where did the third logarithm go? And who is paying for the two that are left?',
      'By the end, you will be able to read this line, and say what every term pays for.',
      { say: 'One warning first. This is a recent preprint. Its main theorem has been machine-checked in Lean, taking ten cited results as given. The constants are enormous, and the algorithm is not practical. The point is what the proof teaches us about where the time goes.', hold: 0.6 },
    ],
    draw(c_, b) {
      c.text('The bill', 640, 120, { size: 30, weight: 600, alpha: b.on(0) });
      const u = b.p(1, 0.15, 0.85);
      D.bill(640, 215, [
        { color: C.violet, alpha: b.on(0) },
        { color: C.violet, alpha: b.on(0) },
        { color: C.red, fill: C.bg2, alpha: b.on(0) * (1 - u * 0.65), strike: u },
      ], { w: 110, h: 54, size: 24 });
      c.tex('\\exp\\big(\\log n\\cdot\\log n\\cdot\\log n\\big)', 640, 300, { size: 26, fill: C.ink2, alpha: b.on(1) * (1 - b.on(3) * 0.4) });
      c.text('Where did the third logarithm go?', 640, 385, { size: 32, weight: 650, alpha: b.on(2) });
      c.text('Who pays for the two that are left?', 640, 427, { size: 26, fill: C.ink2, alpha: b.on(2) });
      D.potential(640, 510, true, { alpha: b.on(3), size: 34 });
      const a = b.on(4);
      c.rect(292, 580, 696, 100, { fill: C.bg2, stroke: C.rule, r: 10, alpha: a, lw: 1.2 });
      c.text('preprint, Nov 2026 (arXiv:2611.01399)', 640, 605, { size: 20, alpha: a });
      c.text('main theorem Lean-checked, modulo 10 cited axioms · constants huge · not practical', 640, 640, { size: 18, fill: C.ink2, alpha: a });
    },
  });
})();
