/* Chapter 17: Phi, term by term. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('terms', 'Φ term by term');
  const CT = 0.1438; // c_theta at theta=3/4, as computed
  V.scene({
    beats: [
      'Open the wallet. Here is the potential in full. Every term has a colour, and a job. We start with the first: x squared, where x is the log of s plus 2.',
      'What does x squared pay for? Suppose a recursive call shrinks the domain by a constant factor, s to theta s, with theta less than 1. Then x falls by a constant. In the paper, by at least c theta equals one half log of 1 over theta, once s is at least 6.',
      'Now watch the square. Take a square of side x, and shave a strip of width c off one side and the top. The area removed is about 2 c x, proportional to x. So the potential falls by about c theta x. This is why it is x squared, and not x: the square turns a constant-size change in x into a drop proportional to x.',
      'And a drop of about x is exactly what buys polynomial branching. Inside a phase, s is above N to the gamma, so log N is at most x over gamma, so N to the a is at most e to the a star x. Polynomial branching, paid in full by one constant-factor shrink.',
      'Same trick for a bigger shrink. If a primitive quotient of degree d gets enumerated, the domain drops by a factor of d, and x squared falls by at least one third of x log d. That pays for up to e to the a log squared d branches, because log d is at most x.',
      { say: 'So here is the first part of the answer. Why x squared? Before I say it, you might try to say it yourself.', hold: 1 },
      'Because each of the two logs in the square is doing a different job. One log, x rounds of constant-factor shrinking. The other log, x bits of branching per round. That is the same bill as before: levels times log of branching.',
    ],
    draw(c_, b) {
      D.potential(640, 58, 0, { alpha: b.on(0), size: 32 });
      const a = b.on(1);
      // Square picture
      const S = 400, X0 = 90, Y0 = 620; // bottom-left origin
      const strip = 70;
      c.rect(X0, Y0 - S, S, S, { fill: C.x2, alpha: a * 0.28, r: 3 });
      c.rect(X0, Y0 - S, S, S, { stroke: C.x2, lw: 2.5, alpha: a, r: 3 });
      c.tex('x', X0 - 18, Y0 - S / 2, { size: 24, alpha: a });
      c.tex('x', X0 + S / 2, Y0 + 24, { size: 24, alpha: a });
      const a2 = b.on(2);
      // remaining square after shave, with u
      const u = b.p(2, 0.15, 0.6);
      const remain = S - strip * u;
      c.rect(X0, Y0 - remain, remain, remain, { fill: C.x2, alpha: a2 * 0.5 });
      // L-shaped strip
      c.rect(X0 + remain, Y0 - S, S - remain, S, { fill: C.orange, alpha: a2 * 0.65 });
      c.rect(X0, Y0 - S, S, S - remain, { fill: C.orange, alpha: a2 * 0.65 });
      c.tex('c_\\theta', X0 + S + 26, Y0 - S + 40, { size: 22, alpha: a2 * u });
      // formulas on right
      const L = 560;
      c.tex('s\\ \\to\\ \\theta s', L, 150, { size: 30, alpha: a, align: 'left' });
      c.tex('x-\\log(\\theta s+2)\\ \\ge\\ c_\\theta=\\tfrac12\\log\\tfrac1\\theta', L, 205, { size: 26, alpha: a, align: 'left' });
      c.tex('x^2-(\\log(\\theta s+2))^2\\ \\ge\\ c_\\theta\\,x', L, 268, { size: 28, alpha: a2, align: 'left', fill: C.x2 });
      const a3 = b.on(3);
      c.tex('s>N^\\gamma\\Rightarrow\\ N^a\\le e^{a_\\ast x},\\quad a_\\ast=a/\\gamma', L, 330, { size: 26, alpha: a3, align: 'left' });
      c.text('polynomial branching, paid in full', L, 370, { size: 21, fill: C.ink2, align: 'left', alpha: a3 });
      const a4 = b.on(4);
      c.tex('x^2-\\log^2(s/d+2)\\ \\ge\\ \\tfrac13\\,x\\log d', L, 430, { size: 26, alpha: a4, align: 'left', fill: C.x2 });
      c.text('pays', L, 473, { size: 21, fill: C.ink2, align: 'left', alpha: a4 });
      c.tex('e^{a\\log^2 d}\\ \\text{ enumeration}', L + 46, 473, { size: 23, alpha: a4, align: 'left' });
      const a6 = b.on(6);
      c.text('x rounds × x bits of branching per round', L, 560, { size: 26, weight: 650, align: 'left', alpha: a6 });
      c.text('Why x², not x? A constant shrink would pay only constant branching.', L, 605, { size: 17, fill: C.ink2, align: 'left', alpha: a6 });
      if (b.in(5, 6)) c.text('(try it: why x²?)', L, 560, { size: 24, fill: C.ink2, align: 'left', alpha: b.on(5, 6) });
    },
  });

  V.scene({
    beats: [
      'Second term: rho x. Here rho is the sum, over levels of the hierarchy, of 2 floor log base 2 of d i, minus 1. It is at most 2 log base 2 of s.',
      'Rho measures how many more times the tower can be refined. Split one ratio into two factors a and b. Floors of logs add at most up to the floor of the log of the product, and the minus 1 gives a strict decrease. So every refinement drops rho by at least 1. Worked out: a product refinement with r factors drops rho by at least r minus 1.',
      'What does that buy? A product refinement branches over at most 2 to the r, r factorial cosets. And log of 2 to the r, r factorial, is at most 4 times r minus 1, times x, since r is at most log s. Rho drops by r minus 1, so rho x drops by r minus 1, times x, and that pays.',
      'Third term, sigma x. Remember the visible unaffected test. Sigma falls by kappa, so sigma x falls by kappa x, and since x is at least gamma log N, that is what pays the polynomially many tests. Sigma is order log s, so this term at the root is order log squared too.',
      'Fourth term, Q. A cap contraction, from at least q down to beta q, on a level with ratio d: Q falls by at least log d times log of 1 over beta. Since d is at least q, that is at least c beta log q. And here is the key: in this case the branching is only q to the a. Everything multiplies against labels, not positions. That is why Q can be measured in log q, and why it fits in log squared.',
      'Finally, B h. The counter h is at most 2, so this term is a constant. It pays for the bounded branching in row constructions that have no immediate domain decrease.',
      'At the root of a phase: x squared is about log squared N. Rho x is at most 2 log base 2 N times log N. Sigma x is order log squared. Q is at most log squared N. And h is at most 2. Everything is order log squared N. The whole wallet is e to the C log squared N.',
    ],
    draw(c_, b) {
      const active = b.in(0, 3) ? 1 : b.in(3, 4) ? 2 : b.in(4, 5) ? 3 : b.in(5, 6) ? 4 : true;
      D.potential(640, 58, active, { alpha: b.on(0), size: 32 });
      const cards = [
        { y: 120, on: 0, off: 3, col: C.rho, title: 'ρx: tower refinement', tex: '\\rho=\\sum_i\\big(2\\lfloor\\log_2 d_i\\rfloor-1\\big)\\le 2\\log_2 s',
          sub: '', tex2: '\\text{split }d=ab:\\ \\ \\lfloor\\log_2 a\\rfloor+\\lfloor\\log_2 b\\rfloor\\le\\lfloor\\log_2 ab\\rfloor', tex3: '\\log(2^r r!)\\le r\\log 2r\\le 4(r-1)x' },
        { y: 120, on: 3, off: 4, col: C.sig, title: 'σx: visible same-domain steps', tex: '\\sigma\\ \\to\\ \\sigma-\\kappa\\quad\\Rightarrow\\quad \\Delta(\\sigma x)\\ge\\kappa x', sub: 'pays the polynomially many tests, with σ = O(log s)' },
        { y: 120, on: 4, off: 5, col: C.Q, title: 'Q: a cap falls', tex: 'c\\ge q\\to c\'\\le\\beta q:\\quad \\Delta Q\\ge(\\log d)\\log\\tfrac1\\beta\\ge c_\\beta\\log q', sub: 'pays q^a continuations: same domain, only labels branch' },
        { y: 120, on: 5, off: 6, col: C.h, title: 'Bh: row-construction events', tex: 'h\\in\\{0,1,2\\},\\quad\\Delta(Bh)=B', sub: 'pays bounded parity choices in row steps' },
      ];
      cards.forEach((cd) => {
        const al = b.on(cd.on, cd.off);
        if (al <= 0) return;
        D.card(120, cd.y, 1040, 410, { alpha: al, stroke: cd.col, lw: 2.5 });
        c.text(cd.title, 640, cd.y + 50, { size: 28, weight: 650, alpha: al });
        c.tex(cd.tex, 640, cd.y + 130, { size: 30, alpha: al });
        if (cd.tex2) c.tex(cd.tex2, 640, cd.y + 215, { size: 25, alpha: al });
        if (cd.tex3) c.tex(cd.tex3, 640, cd.y + 305, { size: 27, alpha: al, fill: C.rho });
        if (cd.sub) c.text(cd.sub, 640, cd.y + 215, { size: 22, fill: C.ink2, alpha: al });
      });
      const a6 = b.on(6);
      if (a6 > 0) {
        c.text('at the root of a phase', 640, 138, { size: 26, weight: 650, alpha: a6 });
        const rows = [
          ['x^2', '\\approx \\log^2 N', C.x2],
          ['\\rho x', '\\le 2\\log_2 N\\cdot\\log N', C.rho],
          ['\\sigma x', '\\le C\\log N\\cdot\\log N', C.sig],
          ['Q', '\\le \\log^2 N', C.Q],
          ['Bh', '\\le 2B', C.h],
        ];
        rows.forEach(([t, r, col], i) => {
          const y = 195 + i * 62;
          c.tex(t, 400, y, { size: 30, fill: col, alpha: a6, key: 'rt' + i });
          c.tex(r, 480, y, { size: 26, align: 'left', alpha: a6, key: 'rr' + i });
        });
        c.tex('\\Rightarrow\\ \\ \\Phi(\\text{root})=O(\\log^2 N)', 640, 548, { size: 36, alpha: a6 });
      }
    },
  });
})();
