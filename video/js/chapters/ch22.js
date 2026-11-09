/* Chapter 22: the Lambda accounting. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('lambda', 'The Λ accounting');
  const TERM = (i) => [C.x2, C.rho, C.sig, C.Q, C.h][i];

  // Potential with Lambda.
  function potentialL(cx, y, active, o = {}) {
    const size = o.size || 30; const a = o.alpha ?? 1;
    const parts = [
      { t: '\\Phi_\\Lambda = A(', col: C.ink, w: 120 },
      { t: '\\Lambda x', col: C.x2, id: 0, w: 58 },
      { t: '+', col: C.ink, w: 28 },
      { t: o.ell ? '\\rho\\,\\ell_N' : '\\Lambda\\rho', col: C.rho, id: 1, w: 58 },
      { t: '+', col: C.ink, w: 28 },
      { t: '\\Lambda\\sigma', col: C.sig, id: 2, w: 58 },
      { t: '+', col: C.ink, w: 28 },
      { t: 'Q_d', col: C.Q, id: 3, w: 52 },
      { t: ')+', col: C.ink, w: 40 },
      { t: 'Bh', col: C.h, id: 4, w: 44 },
    ];
    let x = cx - parts.reduce((s, p) => s + (p.w * size) / 30, 0) / 2;
    parts.forEach((p, i) => {
      const w = (p.w * size) / 30;
      const lit = p.id != null && (active === true || active === p.id);
      const al = a * (p.id != null && active != null && active !== true && !lit ? 0.32 : 1);
      if (lit) c.rect(x - 4, y - size * 0.8, w + 8, size * 1.6, { fill: p.col, alpha: a * 0.16, r: 6 });
      c.tex(p.t, x + w / 2, y, { size, fill: p.col, alpha: al, key: 'potL' + i + (o.ell ? 'e' : '') });
      x += w;
    });
  }

  V.scene({
    beats: [
      'In the main analysis, the same x paid for everything. It worked because N to the a is e to the a star x. Polynomial branching in N was always the reason x sat in the potential.',
      'Now rewrite each row with the true multiplicity, and see what happens when the group lives in the class. Every giant has q at most d, so the branches are about labels, and labels are few. The multiplicities become polynomial in d rather than in N.',
      'So let us replace that x. Introduce Lambda, equal to the log of 8 times max of d and 6, so roughly log d. New potential: A times, Lambda x, plus rho times ell, plus Lambda sigma, plus Q d, then B h.',
      'Note the rho term stays at ell for now. Ell is about log log N. Q d is the cap moment with caps initialized at min of d i and d. And in fact we will get rid of ell shortly.',
      'Row by row. A domain shrink by a constant still drops x by a constant, so Lambda x falls by Lambda times c theta. And that pays for polynomial in d.',
      'Same pattern for sigma. Lambda sigma falls by kappa Lambda, paying d to the order kappa. Q d is unchanged in form. The whole table has moved from log of N, to log of d.',
    ],
    draw(c_, b) {
      D.title('Replace the x that paid for N^{a}', { alpha: b.on(0) });
      const a = b.on(0);
      c.tex('N^a=e^{a\\log N}\\le e^{a_\\ast x}', 640, 110, { size: 32, alpha: a });
      c.text('this is why x sits in Φ', 640, 150, { size: 20, fill: C.ink2, alpha: a });
      const a1 = b.on(1);
      c.tex('q\\le d\\ \\Rightarrow\\ \\text{branches}\\approx q^{O(\\kappa)},\\ \\text{ polynomial in } d', 640, 210, { size: 27, alpha: a1 });
      const a2 = b.on(2);
      c.tex('\\Lambda=\\log(8\\cdot\\max(d,6))', 640, 275, { size: 30, alpha: a2, fill: C.ink });
      potentialL(640, 342, true, { alpha: a2, size: 34, ell: true });
      const a3 = b.on(3);
      c.tex('\\ell_N\\approx\\log\\log N', 420, 400, { size: 23, alpha: a3 });
      c.tex('Q_d:\\ c_i=\\min(d_i,d)', 860, 400, { size: 23, alpha: a3, fill: C.Q });
      const a4 = b.on(4);
      c.tex('\\Delta(\\Lambda x)\\ge\\Lambda\\, c_\\theta', 300, 470, { size: 28, alpha: a4 });
      c.text('pays', 480, 470, { size: 21, fill: C.ink2, alpha: a4 });
      c.tex('d^{O(\\kappa)}', 545, 470, { size: 28, alpha: a4 });
      const a5 = b.on(5);
      c.tex('\\Delta(\\Lambda\\sigma)\\ge\\kappa\\Lambda', 800, 470, { size: 28, alpha: a5 });
      c.tex('d^{O(\\kappa)}', 1020, 470, { size: 28, alpha: a5 });
      D.chip('re-accounting: NOT machine-checked', 640, 560, { alpha: b.on(2), stroke: C.red, size: 19, textFill: C.ink });
      D.chip('not in the HJ paper', 1110, 92, { alpha: a, stroke: C.orange, textFill: C.ink, size: 17 });
    },
  });

  V.scene({
    beats: [
      'But wait. Doesn\'t a certificate make order s calls? The window can update many times. The original table charged N to the a for exactly that reason. If the true multiplicity is polynomial in q, where did those s calls go?',
      'Look at the windows. Fix a test, a colouring, and a type of update. Each update adds new positions, disjoint from the earlier ones. So all the window calls for that fixed test and fixed coset sit on disjoint domains.',
      'And disjoint domains are exactly what the weight prefactor can absorb. Remember, s j plus 2 to the D add up to at most s plus 2 to the D. So all those calls form a single family, a single branch of the weight.',
      'That leaves only the families to count. Two for each test and each coset of the alternating group, doubled for the type of update, and four for each comparison pair. Up to a constant, q to the 2 kappa. That is the regrouping: order q to the 2 kappa families, not order s calls.',
      'This matches the interface in the Lean formalization of the original lemma exactly: a branch only has to satisfy the sum of child sizes at most the parent. Nothing in the original induction is changed. Only what is called a branch.',
    ],
    draw(c_, b) {
      D.title('Regrouping certificate calls', { alpha: b.on(0) });
      const a = b.on(1);
      // Strip of domain with window increments as disjoint segments.
      const X0 = 150, Y0 = 170, W0 = 980, H0 = 44;
      c.rect(X0, Y0, W0, H0, { stroke: C.ink3, lw: 2, r: 4, alpha: a });
      c.text('Ω, all s positions', X0 + W0 / 2, Y0 - 22, { size: 20, fill: C.ink2, alpha: a });
      const seg = [[0, 0.22, C.blue], [0.22, 0.38, C.orange], [0.38, 0.62, C.aqua], [0.62, 0.78, C.yellow], [0.78, 1.0, C.mag]];
      seg.forEach(([u0, u1, col], i) => { const al = D.ease(Math.min(1, (b.t - b.s(1)) / b.d(1) * 5 - i * 0.8)); c.rect(X0 + u0 * W0 + 2, Y0 + 3, (u1 - u0) * W0 - 4, H0 - 6, { fill: col, alpha: al * a, r: 3 }); c.tex('V_' + i, X0 + (u0 + u1) / 2 * W0, Y0 + H0 + 18, { size: 21, alpha: al * a }); });
      const a2 = b.on(2);
      c.tex('\\sum_i (s_i+2)^D\\le(s+2)^D', 640, 300, { size: 32, alpha: a2 });
      c.text('all the window calls for one test: one branch', 640, 345, { size: 23, weight: 600, alpha: a2 });
      const a3 = b.on(3);
      D.card(170, 390, 940, 170, { alpha: a3 });
      c.tex('\\underbrace{2\\binom{q}{\\kappa}\\frac{\\kappa!}{2}\\cdot 2}_{\\text{tests}\\times\\text{cosets}\\times\\text{types}}\\ +\\ \\underbrace{4q^{2\\kappa}}_{\\text{comparisons}}\\ =\\ O(q^{2\\kappa})\\ \\text{ families, not } s\\text{ calls}', 640, 470, { size: 26, alpha: a3 });
      c.text('Lean: PhaseTree.Hyp.branch_disjoint only asks child sizes sum to ≤ s', 640, 610, { size: 20, fill: C.ink2, alpha: b.on(4) });
    },
  });

  V.scene({
    beats: [
      'Now the enumeration channel, which is the one that really is forced. Grohe, Neuen and Schweitzer proved a structure theorem for this class. A primitive group of degree d prime in the class either has order at most d prime to the c one log d, plus c two, or it has a very specific form: a socle that is a power of a Johnson group, Alt m acting on t-subsets, with a big enough parameter.',
      'So in the first case, enumerating costs e to the c one log d times log d prime. Remember the drop for shrinking by d prime: one third of Lambda log d prime. Lambda is about log d. So one third Lambda log d prime pays for it, up to the constant A.',
      'In the second case we must not enumerate. Here the corrected dispatcher rule comes in: recognize the group, and do product refinement and the giant step, if and only if the socle is a Johnson power in product action with m greater than 4 log base 2 of m choose t, and m is greater than the constant q zero. Otherwise enumerate. This test is structural and does not even need to know d.',
      'The original Theorem 3.13 is stated with order conditions too, but the fix here is the structural test: that is how the red-team corrected the dispatcher, and the corrected form is what I am presenting.',
      'What about product refinement? The index was 2 to the r times r factorial, and that gives log r, a log log n term. In this class, the top group is a subgroup of Sym r that also lies in the class. Babai, Cameron and Pálfy bound such a group by d to the r minus 1.',
      'So the index is at most 2 to the r, times d plus 1 to the r minus 1, whose log is at most r minus 1, times Lambda. And rho still falls by r minus 1. So rho times Lambda pays. That is the ell in the potential replaced by Lambda, and no log log n term survives.',
    ],
    draw(c_, b) {
      D.title('Enumeration, and the dispatcher', { alpha: b.on(0) });
      const a = b.on(0);
      c.text('GNS Theorem 3.13 (primitive group of degree d′ in \\hat{Γ}_{d})', 640, 96, { size: 22, weight: 600, alpha: a });
      D.card(70, 130, 540, 180, { alpha: a, stroke: C.aqua });
      c.text('order bound', 340, 165, { size: 22, weight: 600, alpha: a });
      c.tex("|P|\\le d'^{\\,c_1\\log d+c_2}", 340, 225, { size: 30, alpha: a });
      c.text('enumerate it', 340, 280, { size: 20, fill: C.ink2, alpha: a });
      D.card(670, 130, 540, 180, { alpha: a, stroke: C.orange });
      c.text('or: structural', 940, 165, { size: 22, weight: 600, alpha: a });
      c.tex('\\mathrm{Soc}(P)\\cong(A_m^{(t)})^k,\\ \\text{product action}', 940, 225, { size: 26, alpha: a });
      c.tex('m>4\\log_2\\binom mt', 940, 268, { size: 23, alpha: a });
      const a1 = b.on(1);
      c.tex("\\tfrac13\\,\\Lambda\\log d'\\ \\ge\\ c_1\\log d\\,\\log d'\\quad(\\text{up to constants})", 640, 360, { size: 25, alpha: a1 });
      const a2 = b.on(2);
      D.card(70, 400, 1140, 92, { alpha: a2, stroke: C.red });
      c.text('Corrected dispatcher rule (structural test; red-team form):', 640, 426, { size: 21, weight: 600, alpha: a2 });
      c.tex('\\text{recognize, product-refine, GiantStep} \\iff \\mathrm{Soc}(P)\\cong(A_m^{(t)})^k \\text{ in product action},\\ m>4\\log_2\\binom mt,\\ m>q_0;\\ \\text{ else enumerate}', 640, 464, { size: 21, alpha: a2 });
      const a4 = b.on(4), a5 = b.on(5);
      c.tex('2^r\\,r!\\quad\\to\\quad 2^r(d+1)^{r-1}', 340, 535, { size: 30, alpha: a4 });
      c.text('Babai–Cameron–Pálfy: |top group| ≤ d^{r−1}, for d ≥ 6', 340, 585, { size: 19, fill: C.ink2, alpha: a4 });
      c.tex('\\log(\\text{index})\\le(r-1)\\Lambda\\ \\Rightarrow\\ \\rho\\text{ pays},\\ \\text{no }\\log\\log n', 880, 548, { size: 26, alpha: a5 });
      D.chip('not machine-checked', 1110, 94, { alpha: a, stroke: C.red, size: 15, textFill: C.ink });
      if (b.in(5)) potentialL(640, 650, true, { alpha: b.on(5), size: 34 });
    },
  });
})();
