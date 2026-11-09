/* Chapter 14: complete cosets. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('cosets', 'Complete cosets');
  function branch(x, y, depth, spread, o) {
    if (depth === 0) return;
    const n = o.fan;
    for (let i = 0; i < n; i++) {
      const dx = (i - (n - 1) / 2) * spread;
      const nx = x + dx, ny = y + 90;
      c.line(x, y + 8, nx, ny - 8, { stroke: o.col, lw: 1.6, alpha: o.alpha });
      c.circle(nx, ny, 6, { fill: o.col, alpha: o.alpha });
      branch(nx, ny, depth - 1, spread / (n + 0.2), o);
    }
  }
  V.scene({
    beats: [
      'One design decision has been sitting quietly in the background, and now it earns its keep. Every call returns its complete answer: one isomorphism and generators, or the empty set.',
      'Suppose instead an auxiliary call found a single isomorphism and handed it back. Then the parent would need to retry, once for every possibility the auxiliary hid. Its branching multiplies. Depth times depth.',
      'With complete answers, the auxiliary call finishes first, and returns its entire coset. The parent then continues once, under that one coset. The work adds.',
      'So even when a rectangle query does a big search internally, that search is a one-time additive cost. The auxiliary leaves do not each spawn a continuation of the parent.',
      'Two more details from the paper. First, an answer may be an overcoset: it can contain extras that are not real isomorphisms, like the extension over the unconstrained labels. That is fine. The parent re-checks the original colours, and the extras die there.',
      'Second, CombineExact: when an exhaustive family of branches each returns a coset, the union is again a coset, given by one survivor, the stabilizer generators, and the ratios between survivors. Complete answers compose.',
    ],
    draw(c_, b) {
      D.title('Why every call returns its whole answer', { alpha: b.on(0) });
      const a1 = b.on(1), a2 = b.on(2);
      c.circle(350, 150, 9, { fill: C.bg3, stroke: C.ink2, alpha: a1 });
      branch(350, 150, 3, 110, { fan: 3, col: C.red, alpha: a1 });
      c.text('single answers: branching multiplies', 350, 590, { size: 21, alpha: a1 });
      c.tex('\\text{cost}\\approx M_1 \\cdot M_2', 350, 625, { size: 24, alpha: a1 });
      c.circle(960, 150, 9, { fill: C.bg3, stroke: C.ink2, alpha: a2 });
      // aux tree: small, finishes first
      c.circle(960, 240, 8, { fill: C.aqua, alpha: a2 });
      c.line(960, 158, 960, 232, { stroke: C.aqua, lw: 2.5, alpha: a2 });
      branch(960, 240, 2, 44, { fan: 3, col: C.aqua, alpha: a2 * 0.9 });
      c.text('auxiliary', 1090, 245, { size: 19, fill: C.ink2, align: 'left', alpha: a2 });
      c.line(960, 158, 790, 420, { stroke: C.blue, lw: 4, alpha: a2 });
      c.circle(790, 420, 9, { fill: C.blue, alpha: a2 });
      c.text('the parent continues once', 790, 450, { size: 19, alpha: a2 });
      c.text('complete answers: costs add', 960, 590, { size: 21, alpha: a2 });
      c.tex('\\text{cost}\\approx M_1 + M_2', 960, 625, { size: 24, alpha: a2 });
      const a4 = b.on(4), a5 = b.on(5);
      if (b.t >= b.s(4)) {
        c.rect(100, 100, 1080, 460, { fill: C.bg, alpha: Math.max(a4, 0) });
        D.card(100, 110, 520, 300, { alpha: a4 });
        c.text('Overcoset', 360, 155, { size: 26, weight: 650, alpha: a4 });
        c.text('contains every real isomorphism,', 360, 205, { size: 21, alpha: a4 });
        c.text('possibly some extras', 360, 235, { size: 21, alpha: a4 });
        c.text('extras die at the colour re-check', 360, 300, { size: 21, weight: 600, alpha: a4 });
        D.card(660, 110, 520, 300, { alpha: a5 });
        c.text('CombineExact', 920, 155, { size: 26, weight: 650, alpha: a5 });
        c.tex('H\\pi_1\\cup H\\pi_2\\cup\\dots', 920, 215, { size: 28, alpha: a5 });
        c.text('one representative, plus stabilizer', 920, 280, { size: 20, alpha: a5 });
        c.text('generators, plus ratios of survivors', 920, 310, { size: 20, alpha: a5 });
      }
    },
  });
})();
