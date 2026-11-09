/* Chapter 15: the phase structure. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('phases', 'Phases');
  V.scene({
    beats: [
      'Time to step back, and look at the overall shape of the recursion. It is organized into phases.',
      'A phase starts at some size N, and it fixes N and lambda, equal to N to the alpha. Everything inside the phase is measured against those fixed values, however small the current domain becomes.',
      'A call inside the phase inherits the hierarchy and caps, and carries on. It only ends the phase when the domain drops to at most N to the gamma positions. Only there does a fresh phase begin, with fresh hierarchy and fresh caps.',
      'Three things may start a fresh phase: the normal threshold N to the gamma; small configuration solved on at most N to the 2 alpha positions; and calls on single rows, on at most N to the 1 minus alpha positions. Each of them is below N to the gamma.',
      'The paper chooses alpha equals 2 fifths and gamma equals 9 tenths. Any alpha between 1 third and 1 half works, as long as 2 alpha is below gamma and gamma is below 1. The inequalities say that every kind of fresh call really is smaller.',
      'And this is the point: inside a phase, nothing changes the budget. Refinement, column changes, new auxiliary descriptions, none of them restart anything. A phase is one single pot of money.',
    ],
    draw(c_, b) {
      D.title('A phase, on a logarithmic ruler', { alpha: b.on(0) });
      const x0 = 150, x1 = 1130, y = 310;
      const a = b.on(0);
      c.line(x0, y, x1, y, { stroke: C.ink3, lw: 3, alpha: a });
      const X = (u) => lerp(x0, x1, u);
      const tick = (u, label, tex2, col, on, low, lift = 0) => {
        const al = b.on(on);
        const yy = low ? y + 80 : y - 80 - lift;
        c.line(X(u), y - 14, X(u), y + 14, { stroke: col || C.ink2, lw: 3, alpha: al });
        c.line(X(u), y + (low ? 14 : -14), X(u), yy + (low ? -20 : 20), { stroke: col || C.ink2, lw: 1.5, dash: [4, 4], alpha: al });
        c.tex(label, X(u), low ? yy : yy - 8, { size: 27, alpha: al, key: 'tick' + u });
        if (tex2) c.text(tex2, X(u), yy + (low ? 34 : -40), { size: 17, fill: C.ink2, alpha: al });
      };
      tick(1.0, 'N', 'phase start', C.blue, 1, false);
      tick(0.9, 'N^{\\gamma}', 'fresh phase below here', C.blue, 2, false, 56);
      tick(0.8, 'N^{2\\alpha}', 'small configurations', C.aqua, 3, true);
      tick(0.6, 'N^{1-\\alpha}', 'row calls', C.aqua, 3, true);
      tick(0.4, '\\lambda=N^{\\alpha}', 'label threshold', C.lab, 1, false);
      c.text('positions, on a log scale', (x0 + x1) / 2, y + 140, { size: 18, fill: C.ink2, alpha: a });
      const a4 = b.on(4);
      D.card(190, 490, 900, 80, { alpha: a4 });
      c.tex('\\tfrac13<\\alpha<\\tfrac12,\\quad 2\\alpha<\\gamma<1,\\quad \\text{e.g. } \\alpha=\\tfrac25,\\ \\gamma=\\tfrac9{10}', 640, 530, { size: 26, alpha: a4 });
      c.text('a phase is one single pot of money', 640, 640, { size: 28, weight: 650, alpha: b.on(5) });
      // the shaded phase band
      const a2 = b.on(2);
      c.rect(X(0.9), y - 8, X(1) - X(0.9), 16, { fill: C.blue, r: 4, alpha: 0.5 * a2 });
      c.text('inside the phase', X(0.95), y + 40, { size: 19, weight: 600, alpha: a2 });
    },
  });
})();
