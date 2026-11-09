/* Chapter 8: the bill for log^3. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('log3', 'The bill for log³');
  V.scene({
    beats: [
      'Helfgott wrote out the accounting for the corrected algorithm carefully. I will show you his recurrence, because every term of it is going to come back.',
      'Here k is about 2 log n. F of n and r is the time for strings of length n, with a block hierarchy whose remaining depth is measured by r. And m is the number of labels.',
      'First two terms: computing certificates. There are about n to the k test sets, and comparisons between them. Each is a call on a domain smaller by a factor of k.',
      'Last term: the coloured structure on labels. Design Lemma chooses a tuple of up to k labels. That choice isn\'t canonical, so its cost, m to the k, multiplies everything that comes after. Split-or-Johnson does the same, with m to the log m choices.',
      'Pulled together: a cost of about exp of log squared n per round. Each round either lowers r by one or halves n, and r is at most 2 log base 2 of n, so there are at most about 3 log base 2 of n rounds.',
    ],
    draw(c_, b) {
      D.title('Helfgott\'s recurrence (Appendix A)', { alpha: b.on(0) });
      const a = b.on(0);
      c.tex('F(n,r)\\le n^{O(k)}+O(kn^{2k+2}F(\\tfrac nk,r))+m^{O(\\log n)}\\!\\big(1+F(n_1,r{-}1)+\\sum_{i\\ge2}F(n_i,r)\\big)', 640, 160, { size: 25, alpha: a });
      const pts = [
        { x: 380, y: 245, tex: 'k\\approx 2\\log n', sub: 'test-set size', fill: C.lab, on: 1 },
        { x: 640, y: 245, tex: 'n^{2k}\\approx e^{(\\log n)^2}', sub: 'tests and comparisons', fill: C.violet, on: 2 },
        { x: 960, y: 245, tex: 'm^{\\log n}\\approx e^{(\\log n)^2}', sub: 'Design Lemma, Split-or-Johnson', fill: C.violet, on: 3 },
      ];
      pts.forEach((p) => {
        const al = b.on(p.on);
        D.card(p.x - 165, p.y - 35, 330, 110, { alpha: al, stroke: p.fill });
        c.tex(p.tex, p.x, p.y + 2, { size: 25, alpha: al });
        c.text(p.sub, p.x, p.y + 48, { size: 18, fill: C.ink2, alpha: al });
      });
      const a4 = b.on(4);
      c.tex('\\text{cost per round } e^{O(\\log^2 n)}\\quad\\times\\quad r+\\log_2 n\\le 3\\log_2 n\\ \\text{rounds}', 640, 420, { size: 28, alpha: a4 });
      c.tex('F(n,r)\\le e^{O(\\log^3 n)}', 640, 480, { size: 34, alpha: a4, fill: C.ink });
    },
  });

  V.scene({
    beats: [
      'So now the three factors on our bill have names.',
      'One logarithm is the number of rounds: how many times you can cut the group down. That one is about log n, and it is hard to avoid.',
      'A second logarithm is how many labels you have to specify at once: the size of a test set, or the tuple length in the Design Lemma, or the depth of Split-or-Johnson.',
      'The third is the price of naming one label: log m bits, one of m choices.',
      'Each round pays for naming about log n labels, which costs exp of log squared n, and there are about log n rounds. Exp of log cubed.',
      'And every one of the three contributions to that second factor came from something Babai needed. The test sets had to be large because of the unaffected stabilizers. The Design Lemma tuple came with them. The next chapters are about removing that factor.',
    ],
    draw(c_, b) {
      D.title('Three logarithms, three jobs', { alpha: b.on(0) });
      const tiles = [
        { tex: '\\log n', sub: 'rounds', sub2: 'of cutting the giant down', col: C.blue },
        { tex: '\\log n', sub: 'labels named at once', sub2: 'test sets, Design tuple, SoJ depth', col: C.lab },
        { tex: '\\log n', sub: 'bits per label', sub2: 'one of m choices', col: C.aqua },
      ];
      const X = [240, 640, 1040];
      tiles.forEach((t, i) => {
        const al = b.on(i + 1);
        D.card(X[i] - 165, 150, 330, 210, { alpha: al, stroke: t.col });
        c.tex(t.tex, X[i], 215, { size: 38, alpha: al, key: 'big' + i });
        c.text(t.sub, X[i], 290, { size: 22, weight: 600, alpha: al });
        c.text(t.sub2, X[i], 325, { size: 18, fill: C.ink2, alpha: al });
      });
      c.text('×', 440, 240, { size: 34, fill: C.ink3, alpha: b.on(2) });
      c.text('×', 840, 240, { size: 34, fill: C.ink3, alpha: b.on(3) });
      const a4 = b.on(4);
      c.tex('e^{\\log n\\,\\cdot\\,\\log n\\,\\cdot\\,\\log n}', 640, 445, { size: 44, alpha: a4 });
      const a5 = b.on(5);
      c.line(460, 470, 830, 470, { stroke: C.lab, lw: 0, alpha: 0 });
      c.text('the second tile is the one to remove', 640, 545, { size: 26, weight: 600, alpha: a5 });
      D.simplified(640, 610, b.on(1), 'my framing of Helfgott\'s recurrence, not his');
    },
  });
})();
