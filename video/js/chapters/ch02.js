/* Chapter 2: colour refinement. */
(function () {
  const { C, c } = V; const D = window.Dr; const DATA = window.DATA;
  V.chapter('refine', 'Colour refinement');
  const pal = () => [C.blue, C.orange, C.aqua, C.yellow, C.mag, C.green, C.violet, C.red];
  const ex = DATA.cr_example;
  const pos = D.circle(8, 390, 380, 220);

  V.scene({
    beats: [
      'The simplest idea is to let every vertex describe itself.',
      'Start with one colour. Then recolour each vertex by its own colour, together with the multiset of colours of its neighbours.',
      'One round in, vertices with different degrees already look different.',
      'Repeat. A class can split, but two vertices that were told apart stay apart. So this has to stop.',
      'Here it stops with every vertex holding a colour of its own.',
      'If the colours are all distinct on two graphs, comparing them is immediate. The colours tell us which vertex must map to which, and then we just check the edges.',
      'This is colour refinement, and on almost every graph you will ever meet, it finishes the job in near-linear time.',
    ],
    draw(c_, b) {
      D.title('Colour refinement, on a real graph', { alpha: b.on(0) });
      const rounds = ex.rounds, maxr = rounds.length - 1;
      // which round are we displaying
      const shown = [b.in(1) ? 1 : 0, b.in(2) ? 1 : 0, b.in(3) ? 1 : 0, b.in(4) ? 1 : 0];
      let r = 0;
      if (b.t > b.s(1) + 0.3) r = 0; if (b.t > b.s(2)) r = 1; if (b.t > b.s(3)) r = 2; if (b.t > b.s(3) + b.d(3) * 0.55) r = 3; if (b.t > b.s(4)) r = maxr;
      const col = (i) => pal()[rounds[r][i] % 8];
      D.graph(pos, ex.edges, { r: 20, fill: (i) => b.t < b.s(1) ? C.bg3 : col(i), alpha: b.on(0), labelFill: '#111' });
      // right side: round / class bar
      const a = b.on(2);
      c.text('round ' + (b.t < b.s(2) ? 0 : b.t < b.s(3) ? 1 : r), 980, 120, { size: 26, weight: 600, alpha: b.on(1) });
      const ks = ex.classes;
      const kk = ks[Math.min(r, ks.length - 1)];
      c.text('colour classes: ' + kk + ' of 8', 980, 158, { size: 20, fill: C.ink2, alpha: b.on(1) });
      for (let i = 0; i < 8; i++) c.rect(840 + i * 36, 188, 30, 30, { fill: i < kk ? pal()[i] : C.bg3, r: 5, alpha: b.on(1) });
      // show the multiset sentence for the highlighted vertex
      const v = 3;
      const nb = [];
      ex.edges.forEach(([x, y]) => { if (x === v) nb.push(y); else if (y === v) nb.push(x); });
      const al = b.on(1, 3);
      if (al > 0) {
        c.circle(pos[v][0], pos[v][1], 25, { stroke: C.ink, lw: 3, alpha: al });
        nb.forEach((u) => c.line(pos[v][0], pos[v][1], pos[u][0], pos[u][1], { stroke: C.ink, lw: 4, alpha: al * 0.5 }));
        c.tex('c_{\\text{new}}(v) = \\big(c(v),\\ \\{\\!\\{\\,c(u) : u\\sim v\\,\\}\\!\\}\\big)', 960, 340, { size: 24, alpha: al });
      }
      if (b.on(5) > 0) { c.text('compare by colour, then check edges', 960, 340, { size: 22, fill: C.ink, alpha: b.on(5) * (1 - b.on(6)) }); }
      c.text('near-linear time', 960, 340, { size: 24, weight: 600, alpha: b.on(6) });
    },
  });

  const pP = D.petersenPos(320, 390, 190), pQ = D.prismPos(960, 390, 190);
  V.scene({
    beats: [
      'Now run it on our two graphs. Every vertex has three neighbours, all the same colour.',
      'Nothing can split. One colour, forever, on both graphs. And they are not the same graph.',
      { say: 'Can we fix that? Refine ordered pairs of vertices instead, or triples, or k-tuples. Before I answer: do you think looking at large enough tuples must eventually see everything?', hold: 1.5 },
      'In 1992 Cai, Fürer and Immerman showed the answer is no, and the examples are small: graphs of maximum degree three, where the dimension needed grows linearly with the number of vertices.',
      'Let me show you the idea, because the reason is the first real clue about what this problem is.',
    ],
    draw(c_, b) {
      D.title('Where it stops', { alpha: b.on(0) });
      const col = C.aqua;
      D.graph(pP, DATA.petersen.edges, { r: 13, fill: b.t > b.s(1) ? col : C.bg3, alpha: b.on(0) });
      D.graph(pQ, DATA.prism.edges, { r: 13, fill: b.t > b.s(1) ? col : C.bg3, alpha: b.on(0) });
      c.text('one colour, forever', 320, 618, { size: 22, weight: 600, alpha: b.on(1) });
      c.text('one colour, forever', 960, 618, { size: 22, weight: 600, alpha: b.on(1) });
      const a = b.on(2, 3);
      c.rect(380, 110, 520, 90, { fill: C.bg2, stroke: C.rule, r: 10, alpha: a, lw: 1 });
      c.tex('\\text{refine on } k\\text{-tuples: cost } n^{k+O(1)}', 640, 155, { size: 26, alpha: a });
      c.text('Cai, Fürer, Immerman 1992', 640, 130, { size: 22, weight: 600, alpha: b.on(3) * (1 - b.on(4) * 0.3) });
      c.tex('\\text{degree 3, dimension needed } \\Omega(n)', 640, 172, { size: 24, alpha: b.on(3) });
    },
  });
})();
