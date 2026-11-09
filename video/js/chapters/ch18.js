/* Chapter 18: the charging table. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('table', 'The charging table');

  const ROWS = [
    { op: 'Affected test or rectangle', m: 'N^a', drop: 'A c_\\theta x-2B', term: C.x2, why: 'domain shrinks by θ: x² falls by c_θ x' },
    { op: 'Visible unaffected test', m: 'N^a', drop: 'A\\kappa x-2B', term: C.sig, why: 'σ falls by κ: σx falls by κx' },
    { op: 'Product refinement, r ≥ 2', m: 'N^a\\,2^r r!', drop: 'A(r-1)x-2B', term: C.rho, why: 'ρ falls by r−1: ρx falls by (r−1)x' },
    { op: 'Primitive enumeration, degree d', m: 'N^a e^{a\\log^2 d}', drop: '\\tfrac A3 x\\log d-2B', term: C.x2, why: 'domain drops by d: x² falls by ⅓ x log d' },
    { op: 'Auxiliary-graph continuation', m: 'q^a', drop: 'A c_\\beta\\log q-2B', term: C.Q, why: 'cap q→βq: Q falls by c_β log q' },
    { op: 'Row initialization or enlargement', m: 'b_0', drop: 'B', term: C.h, why: 'h falls by one: Bh falls by B' },
  ];
  const Y0 = 150, RH = 74;
  const drawRow = (r, i, a) => {
    const y = Y0 + i * RH;
    if (i % 2 === 0) c.rect(70, y - 34, 1140, RH, { fill: C.bg2, alpha: a * 0.6, r: 5 });
    c.rect(70, y - 34, 6, RH, { fill: r.term, alpha: a });
    c.text(r.op, 92, y + 2, { size: 20, align: 'left', alpha: a, weight: 500 });
    c.tex(r.m, 620, y + 2, { size: 25, alpha: a, key: 'mcol' + i });
    c.tex(r.drop, 900, y + 2, { size: 25, alpha: a, key: 'dcol' + i });
  };

  V.scene({
    beats: [
      'Here is the whole table. Six rows. Each row is one kind of recursive step: how many branches it makes, and how much potential every one of those branches loses.',
      'The minus 2 B in the first five rows allows for a worst-case reset of the counter h.',
      'Row one: an affected test, or a rectangle query. Polynomially many branches, N to the a. The domain shrinks by a constant factor, so x squared pays: A times c theta times x.',
      'Row two: a visible unaffected test. Also polynomial. Sigma falls by kappa, so sigma x falls by kappa x.',
      'Row three: product refinement. Branches 2 to the r, r factorial, against a rho drop of r minus 1.',
      'Row four: enumeration of a primitive quotient of degree d. Branches e to the a log squared d. Here is the one line that looks scary: log squared d. Domain drops by d, so x squared falls by a third of x log d. Since x is at least log d, that covers it.',
      { say: 'Before row five: what do you predict it is? Same domain. One cap falls. What pays?', hold: 1.5 },
      'Row five: the continuation after a rectangle. Only q to the a branches, because branching is over labels. Paid by Q falling by c beta log q.',
      'Row six: a row-construction event has a bounded number b zero of branches. It spends one unit of h, and the weight drops by B.',
    ],
    draw(c_, b) {
      D.title('The charging table', { alpha: b.on(0), y: 38 });
      const a = b.on(0);
      c.text('Recursive operation', 92, Y0 - 58, { size: 19, align: 'left', fill: C.ink2, alpha: a, weight: 600 });
      c.text('Branches', 620, Y0 - 58, { size: 19, fill: C.ink2, alpha: a, weight: 600 });
      c.text('Potential drop', 900, Y0 - 58, { size: 19, fill: C.ink2, alpha: a, weight: 600 });
      ROWS.forEach((r, i) => {
        const on = i + 2 === 7 ? 7 : (i >= 5 ? 8 : i + 2);
        const al = b.t >= b.s(Math.min(on, 8)) ? 1 : 0;
        const showAll = b.in(0, 2);
        const dim = showAll ? 0.4 : 1;
        const shown = showAll ? b.on(0, 2) * 0.4 : (b.on(on) * 1);
        drawRow(r, i, Math.max(shown, 0));
        if (i === 4) {
          // prediction prompt in the beat before row five
          if (b.in(6, 7)) c.text('?', 900, Y0 + i * RH + 2, { size: 36, weight: 700, fill: C.Q, alpha: b.on(6, 7) });
        }
      });
      // explanation for current row
      const cur = b.in(2, 3) ? 0 : b.in(3, 4) ? 1 : b.in(4, 5) ? 2 : b.in(5, 6) ? 3 : b.in(7, 8) ? 4 : b.in(8) ? 5 : -1;
      if (cur >= 0) c.text(ROWS[cur].why, 640, 672, { size: 24, weight: 600, alpha: 1 });
      if (b.in(1, 2)) c.tex('h\\in\\{0,1,2\\}:\\ \\text{worst-case reset costs } 2B', 640, 672, { size: 25, alpha: b.on(1, 2) });
    },
  });

  V.scene({
    beats: [
      'Every row is now one inequality. We need log of the branches, plus a small constant, to be at most the potential drop.',
      'For the domain and sigma rows, since log of N to the a is at most a star x, we need A c theta to be at least a star plus a bit. Same with A kappa.',
      'For the enumeration row we have to be a little more careful, but the check is short: a log squared d, plus a star x, is at most that coefficient times x log d, because x is at least log d, and x at least log 8.',
      'So the conditions are just a handful of inequalities for the single constant A. Those inequalities are listed in the paper, and they are checked in Lean.',
      'Then every class of children carries at most 1 over 8J of the weight, and J is at most 8. Everything fits. The argument is finished.',
    ],
    draw(c_, b) {
      D.title('Every row is one inequality', { alpha: b.on(0) });
      const a = b.on(0);
      c.tex('\\log(\\text{branches})\\ +\\ \\log(8J)\\ \\le\\ \\text{table drop (net of }2B)', 640, 118, { size: 28, alpha: a });
      const eqs = [
        { y: 200, on: 1, tex: 'A\\,c_\\theta\\ \\ge\\ a_\\ast+\\frac{H_\\ast}{x_0},\\qquad A\\,\\kappa\\ \\ge\\ a_\\ast+\\frac{H_\\ast}{x_0}', col: C.ink },
        { y: 275, on: 2, tex: '\\frac A3\\ \\ge\\ a+\\frac{a_\\ast}{\\log2}+\\frac{H_\\ast}{x_0\\log2}', col: C.ink },
        { y: 345, on: 2, tex: 'A\\,c_\\beta\\ \\ge\\ a+\\frac{H_\\ast}{\\log q_0},\\qquad A\\ \\ge\\ 4+a_\\ast+\\frac{H_\\ast}{x_0}', col: C.ink },
      ];
      eqs.forEach((e) => c.tex(e.tex, 640, e.y, { size: 27, alpha: b.on(e.on), fill: e.col }));
      c.tex('H_\\ast=2B+\\log(8J),\\quad x_0=\\log 8,\\quad a_\\ast=a/\\gamma', 640, 420, { size: 23, alpha: b.on(1), fill: C.ink2 });
      const a4 = b.on(4);
      c.tex('\\text{each class carries}\\ \\le\\ \\frac{W}{8J},\\quad J\\le 8', 640, 520, { size: 32, alpha: a4 });
      c.text('Lean: GI.Paper.lem_main_phase_bound', 640, 575, { size: 18, fill: C.ink2, alpha: a4 });
    },
  });
})();
