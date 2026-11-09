/* Chapter 9: constant-size tests, HJ's idea 1. */
(function () {
  const { C, c } = V; const D = window.Dr; const DATA = window.DATA;
  V.part('Part IV: Hajiaghayi and JafariRaviz');
  V.chapter('kappa', 'Constant-size tests');

  V.scene({
    beats: [
      'Here is the first new idea. Use test sets of a fixed size. Kappa equals 64, forever, no matter how large the instance is.',
      'Immediately the number of tests becomes polynomial. There are only q to the 64 of them, for q labels. That is the second tile of the bill, gone, if we can survive it.',
      'And that is the problem we just saw: at this size a test can be invisible. Babai was forced above the threshold. So how do you live below it?',
      'Remember the procedure. Grow a window of positions already checked. The affected positions are handled exactly as before, with a domain that shrinks by a factor of kappa.',
      'What is new is the endpoint. When no position is affected, the algorithm asks one more question. Does the group of relabelings that fix everything outside the window still realize all of Alt(T)?',
      'If yes: those relabelings preserve the checked colours and fix everything else, so they are real automorphisms. A full certificate, exactly as before.',
      'If no: since Alt(T) is simple, the image of that pointwise stabilizer must be trivial, and then some orbit of unchecked positions is seeing the test. In that orbit the test acts visibly. Add it to the window, and restrict to the relabelings that fix every test label.',
    ],
    draw(c_, b) {
      D.title('Constant-size test sets: the new endpoint', { alpha: b.on(0) });
      c.tex('\\kappa = 64', 150, 120, { size: 38, alpha: b.on(0) });
      c.tex('\\binom{q}{\\kappa} \\le q^{64}', 150, 170, { size: 24, alpha: b.on(1), fill: C.ink2 });
      c.text('polynomially many tests', 150, 205, { size: 18, fill: C.ink2, alpha: b.on(1) });
      // flowchart (center-right)
      const cx = 760, x1 = 760;
      const box = (x, y, w, h, label, al, opt) => D.box(x, y, w, h, label, { alpha: al, ...(opt || {}) });
      const a3 = b.on(3);
      box(cx, 120, 460, 50, 'Window of checked positions W', a3, { size: 20 });
      c.arrow(cx, 145, cx, 186, { stroke: C.ink3, alpha: b.on(3) });
      box(cx, 210, 460, 48, 'Any affected position left outside W?', a3, { size: 20 });
      // yes path
      c.arrow(cx + 230, 210, cx + 330, 210, { stroke: C.ink3, alpha: a3 });
      c.text('yes', cx + 270, 195, { size: 18, fill: C.ink2, alpha: a3 });
      box(cx + 390, 210, 100, 66, 'check it', a3, { size: 18 });
      c.text('s/κ', cx + 390, 248, { size: 18, fill: C.ink2, alpha: 0 });
      c.text('domain shrinks ÷κ', cx + 290, 260, { size: 18, fill: C.ink2, alpha: a3 });
      // no path
      const a4 = b.on(4);
      c.line(cx, 234, cx, 268, { stroke: C.ink3, alpha: a4 });
      c.text('no', cx + 16, 256, { size: 18, fill: C.ink2, alpha: a4 });
      box(cx, 290, 520, 50, 'Does the pointwise stabilizer of Ω∖W realize Alt(T)?', a4, { size: 20 });
      // yes full
      const a5 = b.on(5);
      c.arrow(cx - 260, 316, cx - 330, 370, { stroke: C.ink3, alpha: a5 });
      c.text('yes', cx - 275, 342, { size: 18, fill: C.ink2, alpha: a5 });
      D.box(cx - 420, 420, 280, 90, 'Full certificate', { alpha: a5, stroke: C.green, size: 24, weight: 650 });
      c.text('real automorphisms', cx - 420, 452, { size: 18, fill: C.ink2, alpha: a5 });
      // no: visible
      const a6 = b.on(6);
      c.arrow(cx + 200, 316, cx + 300, 370, { stroke: C.ink3, alpha: a6 });
      c.text('no', cx + 262, 342, { size: 18, fill: C.ink2, alpha: a6 });
      D.box(cx + 220, 440, 440, 120, '', { alpha: a6, stroke: C.aqua });
      c.text('An unchecked orbit Δ on which', cx + 220, 402, { size: 20, alpha: a6 });
      c.text('the test acts visibly', cx + 220, 430, { size: 20, weight: 600, alpha: a6 });
      c.text('kernel still transitive on Δ', cx + 220, 462, { size: 18, fill: C.ink2, alpha: a6 });
      c.text('add Δ, fix all test labels', cx + 220, 490, { size: 18, fill: C.ink2, alpha: a6 });
      c.tex('\\mathrm{Alt}(T)\\text{ simple: image trivial}', cx - 40, 660, { size: 21, alpha: a6, fill: C.ink2 });
      // left: warning sign recap
      const a2 = b.on(2, 3);
      D.card(70, 280, 420, 190, { alpha: a2 });
      c.text('Below Babai\'s threshold,', 280, 320, { size: 21, weight: 600, alpha: a2 });
      c.text('a test can be invisible', 280, 350, { size: 21, weight: 600, alpha: a2 });
      c.text('every position unaffected,', 280, 395, { size: 18, fill: C.ink2, alpha: a2 });
      c.text('nothing to recurse on', 280, 425, { size: 18, fill: C.ink2, alpha: a2 });
      D.simplified(150, 256, b.on(3), 'real algorithm, drawn as a flowchart');
    },
  });

  V.scene({
    beats: [
      'Stop and look at what just happened in that last branch.',
      'We restricted the group to the relabelings fixing the test labels, and that restriction can keep the entire orbit. Fixing the labels does not fix any position, the kernel is transitive. The window has grown, but the problem has not become smaller.',
      'So the recursion now has two kinds of calls. The domain shrinks: s goes to s over kappa. Or the domain does not shrink at all, but a certain quantity sigma goes down by kappa.',
      'In the language of the paper, every local test costs polynomially many calls of those two types. And the paper\'s whole claim is that sigma is a resource that cannot run forever.',
      'But why should it be? We just took a step and kept every position. What did we use up? That is the next chapter.',
    ],
    draw(c_, b) {
      D.title('Two kinds of recursive call', { alpha: b.on(0) });
      const a = b.on(2);
      c.tex('(s,\\sigma)\\ \\longmapsto\\ (s/\\kappa,\\ \\sigma)', 640, 300, { size: 40, alpha: a });
      c.tex('(s,\\sigma)\\ \\longmapsto\\ (s,\\ \\sigma-\\kappa)', 640, 395, { size: 40, alpha: a, fill: C.sig });
      c.text('domain shrinks by κ', 1000, 300, { size: 21, align: 'left', fill: C.ink2, alpha: a });
      c.text('domain unchanged, σ drops', 1000, 395, { size: 21, align: 'left', fill: C.ink2, alpha: a });
      // the orbit pictured
      const a1 = b.on(1);
      if (a1 > 0 && b.t < b.e(2)) {
        for (let i = 0; i < 36; i++) { const row = Math.floor(i / 6); c.circle(250 + (i % 6) * 36 + row * 2, 140 + row * 28, 11, { fill: C.pos, alpha: a1 * b.on(1, 2) * 0.85 }); }
        c.text('Δ stays whole', 340, 230, { size: 20, alpha: a1 * b.on(1, 2) });
        c.text('window grew, but problem did not', 800, 180, { size: 23, weight: 600, alpha: a1 * b.on(1, 2) });
      }
      c.text('polynomially many calls of these two types', 640, 480, { size: 24, weight: 600, alpha: b.on(3) });
      c.text('What paid for that second one?', 640, 560, { size: 34, weight: 650, alpha: b.on(4) });
    },
  });
})();
