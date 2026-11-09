/* Chapter 11: hierarchy and caps. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('caps', 'Hierarchy and caps');

  // example hierarchy
  const ratios = [8, 2, 16, 2, 4];         // d_i, product = 2048 (log2 = 11)
  const caps = [8, 2, 16, 2, 4];
  V.scene({
    init: () => ({ }),
    beats: [
      'Second new idea: keep the decomposition, and keep what you learned about it. For a transitive action, the state carries a stack of block systems, with ratios d one through d t that multiply to s.',
      'Each ratio also carries a cap, c i. A promise that this level of the hierarchy can never induce a giant on more than c i labels, even after further restrictions. Initially the cap is just d i.',
      'Here is the crucial new picture. Draw each level as a bar. Its width is log d i. Its height is log of c i. The widths add up to log s.',
      'Now look at the area of all the bars. That quantity is Q: the sum of log d i times log max c i, 2. And the bars all fit inside a square of side log s. So Q is at most log squared s.',
      'A cap can fall without the partition changing. If we learn that the giant at level 3 can\'t act on more than beta q labels, the height of that bar falls. The width does not move. No new block appears, and Q has gone down.',
      'And caps are inherited: when a call restricts to an orbit, it intersects the hierarchy with that orbit, and each level keeps the minimum of its old cap and its new ratio.',
    ],
    draw(c_, b) {
      D.title('A stack of bars whose area is Q', { alpha: b.on(0) });
      const a = b.on(0);
      const total = ratios.map(Math.log2).reduce((p, q) => p + q, 0);
      const W = 480, X0 = 110, Y0 = 620;
      const unit = W / total;
      // Square outline
      const sq = b.on(3);
      c.rect(X0, Y0 - W, W, W, { stroke: C.rule, lw: 2, alpha: sq });
      c.tex('(\\log s)^2', X0 + W - 8, Y0 - W + 22, { size: 24, alpha: sq, align: 'right' });
      // dropping cap on level index 2 (the d=16 interval)
      const drop = b.in(4) ? b.p(4, 0.2, 0.85) : (b.t >= b.s(5) ? 1 : 0);
      let x = X0;
      ratios.forEach((d, i) => {
        const wd = Math.log2(d) * unit;
        const beta = 0.6;
        const hLog = Math.log2(Math.max(caps[i], 2)) * unit;
        const h = i === 2 ? hLog * (1 - drop * (1 - beta)) : hLog;
        const showBars = b.on(2);
        c.rect(x, Y0 - h, wd - 3, h, { fill: C.Q, r: 3, alpha: showBars * 0.9 });
        if (i === 2 && drop > 0) c.line(x, Y0 - hLog, x + wd - 3, Y0 - hLog, { stroke: C.Q, lw: 2, dash: [5, 5], alpha: showBars });
        c.text('d = ' + d, x + wd / 2, Y0 + 20, { size: 15, fill: C.ink2, alpha: a });
        x += wd;
      });
      // label axes
      c.tex('\\log d_i', X0 + W / 2, Y0 + 50, { size: 22, alpha: b.on(2), fill: C.ink2 });
      c.tex('\\log\\max\\{c_i,2\\}', X0 + 8, Y0 - W + 22, { size: 21, alpha: b.on(2), fill: C.ink2, align: 'left' });
      // Right column: hierarchy list
      const lx = 760, a2 = b.on(1);
      c.tex('s = \\prod_i d_i', lx + 170, 130, { size: 28, alpha: a });
      c.text('blocks, with a cap on each level', lx + 170, 168, { size: 18, fill: C.ink2, alpha: a });
      ratios.forEach((d, i) => {
        const y = 220 + i * 44;
        const shownCap = i === 2 && drop > 0.5 ? 'βq' : String(caps[i]);
        c.text('level ' + (i + 1), lx, y, { size: 20, align: 'left', fill: C.ink2, alpha: a2 });
        c.tex('d=' + d, lx + 140, y, { size: 22, alpha: a2 });
        c.tex('c=' + shownCap, lx + 280, y, { size: 22, fill: C.ink, alpha: a2, key: 'cap' + i });
      });
      const a3 = b.on(3);
      c.tex('Q=\\sum_i(\\log d_i)\\log\\max\\{c_i,2\\}\\ \\le\\ (\\log s)^2', lx + 170, 470, { size: 25, alpha: a3 });
      const a4 = b.on(5);
      c.tex('c\'=\\min\\{c,\\ d\'\\}', lx + 170, 570, { size: 30, alpha: a4 });
      c.text('caps are inherited, never reset', lx + 170, 612, { size: 20, fill: C.ink2, alpha: a4 });
    },
  });
  V.scene({
    beats: [
      'What is a cap, precisely? The paper calls it alternating width. The alternating width of a group is the largest k at least 5 with Alt k appearing as a section, that is, a quotient of a subgroup. A cap bounds this for the entire constituent action at that level.',
      'That one word, section, matters. It makes the promise survive subgroup restriction and quotients. Whatever we learn about a level stays true however the group shrinks later.',
      'So now we have three different things that can make progress: the domain can shrink, sigma can fall, and a cap can fall. Each one, on a recursion path, is a finite resource.',
      'The potential is simply a way of adding those resources up. We will get there. First, the other half of the algorithm: how does a cap actually get lowered?',
    ],
    draw(c_, b) {
      D.title('Alternating width', { alpha: b.on(0) });
      const a = b.on(0);
      c.tex('\\mathrm{aw}(A)=\\max\\{\\,k\\ge5:\\ \\mathrm{Alt}(k)\\text{ is a section of }A\\,\\}', 640, 200, { size: 32, alpha: a });
      c.text('section: a quotient of a subgroup', 640, 250, { size: 21, fill: C.ink2, alpha: a });
      const a1 = b.on(1);
      c.tex('\\mathrm{aw}(B)\\le\\mathrm{aw}(A)\\quad\\text{for subgroups and quotients}', 640, 345, { size: 28, alpha: a1 });
      c.text('so the promise survives every later restriction', 640, 395, { size: 21, fill: C.ink2, alpha: a1 });
      const a2 = b.on(2);
      const items = [['domain shrinks', C.x2], ['σ falls', C.sig], ['a cap falls', C.Q]];
      items.forEach(([t, col], i) => {
        const x = 260 + i * 380;
        c.rect(x - 170, 460, 340, 90, { fill: C.bg2, stroke: col, lw: 3, r: 10, alpha: a2 });
        c.text(t, x, 505, { size: 26, weight: 650, alpha: a2 });
      });
      c.text('How does a cap actually get lowered?', 640, 630, { size: 29, weight: 650, alpha: b.on(3) });
    },
  });
})();
