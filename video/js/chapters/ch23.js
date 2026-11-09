/* Chapter 23: the result, sanity limits, the barrier, status. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr; const DATA = window.DATA;
  V.chapter('degree-result', 'n^O(log(d+2)): result and limits');
  V.scene({
    beats: [
      'Add up the wallet at the root, as before. Lambda x, Lambda rho, Lambda sigma, and Q d, are each at most a constant times log N times log d. So the wallet is e to the order log N times Lambda.',
      'The rest of the machine is unchanged. The phase recursion, the weight argument, the geometric series. Phases with d above N to the alpha are handled by the original bound directly, which is at most e to log N times log d, up to a constant.',
      'So string isomorphism for groups in this class costs e to the order log of N plus 2, times log of d plus 2. Graphs of maximum degree d give N equals a polynomial in n. So the whole thing is n to the order log of d plus 2.',
      'Two sanity checks. If d is a constant, this is n to a constant: Luks\'s polynomial-time result. If d is about n, then log of d is about log n, and we get back n to the order log n. The result interpolates between the two.',
      'For comparison, the best published bound here is n to the polylog of d, from Grohe, Neuen, and Schweitzer. So if everything so far is right, this is a real improvement in the exponent.',
    ],
    draw(c_, b) {
      D.title('The degree-d bound', { alpha: b.on(0) });
      D.chip('conditional · not in the HJ paper', 1080, 92, { alpha: b.on(0), stroke: C.red, size: 17, textFill: C.ink });
      const a = b.on(0);
      c.tex('\\Phi_\\Lambda(\\text{root}) = O(\\Lambda\\log N)', 640, 110, { size: 32, alpha: a });
      const a2 = b.on(2);
      c.tex('F_d(N)=\\exp\\big(O(\\log(N+2)\\cdot\\log(d+2))\\big)', 640, 210, { size: 34, alpha: a2 });
      c.tex('\\text{GI of max degree } d:\\quad n^{O(\\log(d+2))}', 640, 280, { size: 36, alpha: a2 });
      const a3 = b.on(3);
      // Sanity limits on a line
      const x0 = 150, x1 = 1130, y = 410;
      c.line(x0, y, x1, y, { stroke: C.ink3, lw: 3, alpha: a3 });
      const pts = [
        { u: 0.05, t: 'd = O(1)', tex: 'n^{O(1)}', sub: 'Luks' },
        { u: 0.5, t: 'd = polylog n', tex: 'n^{O(\\log\\log n)}', sub: '' },
        { u: 0.95, t: 'd ≈ n', tex: 'n^{O(\\log n)}', sub: 'HJ' },
      ];
      pts.forEach((p) => {
        const X = lerp(x0, x1, p.u);
        c.line(X, y - 12, X, y + 12, { stroke: C.ink2, lw: 3, alpha: a3 });
        c.text(p.t, X, y - 35, { size: 20, alpha: a3 });
        c.tex(p.tex, X, y + 44, { size: 26, alpha: a3, key: 'pts' + p.u });
        if (p.sub) c.text(p.sub, X, y + 82, { size: 19, fill: C.ink2, alpha: a3 });
      });
      const a4 = b.on(4);
      D.card(120, 520, 1040, 130, { alpha: a4 });
      c.text('Best published:', 150, 558, { size: 22, weight: 600, align: 'left', alpha: a4 });
      c.tex('n^{\\mathrm{polylog}(d)}', 340, 558, { size: 28, align: 'left', alpha: a4 });
      c.text('Grohe, Neuen, Schweitzer', 150, 610, { size: 20, fill: C.ink2, align: 'left', alpha: a4 });
      D.chip('conditional · not in the HJ paper · see status card', 880, 586, { alpha: a4, stroke: C.red, size: 19, textFill: C.ink });
    },
  });

  const BAR = DATA.barrier;
  V.scene({
    beats: [
      'Can re-analysis push this any further? No. There is an explicit family that forces this algorithm to do the work.',
      'Take D odd, and d equal to D minus 1. Let P be the affine-type group: the even-weight vectors of length D, over F two, extended by Sym D permuting the coordinates. It acts on 2 to the d points, and it is primitive.',
      'Now take the wreath product of P with a cycle of length m, where m is a power of 2, acting in the product action on those d-coordinate vectors, m at a time. N is 2 to the d m positions. The group is in Gamma hat D, and it is primitive.',
      'Its socle is elementary abelian: no Johnson structure, so the corrected dispatcher enumerates it, and so does the original. And its order is at least N to the log base 2 of D minus 0.443.',
      'So on every pair of strings, the algorithm creates at least that many cosets, whatever the colours are. Real numbers: for D equals 9 and m equals 256, the exponent of N is about 3.3. So no re-analysis can give n to the little o of log d, on this algorithm, in the string setting.',
      'Two scope limits. It is the string-isomorphism setting, not graphs. Whether graphs of degree d produce such groups inside this algorithm is not known. And the floor is not intrinsic: a different algorithm that memoizes over block pairs solves this very family in time fixed-parameter in d. The algorithm has to change.',
    ],
    draw(c_, b) {
      D.title('Why this cannot be pushed further by re-analysis', { alpha: b.on(0) });
      D.chip('not in the HJ paper · AI-checked only', 1040, 86, { alpha: b.on(0), stroke: C.red, size: 16, textFill: C.ink });
      const a = b.on(1);
      c.tex('P_d=\\mathbb F_2^{\\,d}\\rtimes\\mathrm{Sym}(D),\\quad D=d+1\\ \\text{odd}', 640, 112, { size: 28, alpha: a });
      const a2 = b.on(2);
      c.tex('G_{d,m}=P_d\\wr C_m,\\quad m=2^j,\\quad N=2^{dm},\\quad G_{d,m}\\in\\hat\\Gamma_D', 640, 165, { size: 28, alpha: a2 });
      const a3 = b.on(3);
      c.tex('|G_{d,m}|\\ \\ge\\ N^{\\log_2 D-0.443}', 640, 228, { size: 34, alpha: a3 });
      // Chart: exponent of N for D=3,5,9,33
      const a4 = b.on(4);
      const rows = [[3, 2], [5, 2], [9, 2], [33, 2]].map(([D2]) => {
        const r = BAR.filter((x) => x.D === D2 && x.m === 256)[0];
        return r;
      });
      const X0 = 200, Y0 = 500, bw = 150, maxv = 5.5, H = 200;
      rows.forEach((r, i) => {
        const x = X0 + i * bw;
        const h = (r.exponent / maxv) * H;
        c.rect(x, Y0 - h, 90, h, { fill: C.red, r: 3, alpha: a4 * 0.85 });
        c.text(r.exponent.toFixed(2), x + 45, Y0 - h - 16, { size: 20, weight: 600, alpha: a4 });
        c.text('D=' + r.D, x + 45, Y0 + 20, { size: 19, fill: C.ink2, alpha: a4 });
      });
      c.tex('\\log_N|G|', 110, 400, { size: 22, alpha: a4, fill: C.ink2 });
      c.text('computed exponent, m = 256', X0 + 210, Y0 + 60, { size: 18, fill: C.ink2, alpha: a4 });
      c.text('forced coset branches', 900, 350, { size: 21, fill: C.ink2, alpha: a4 });
      c.tex('\\ge N^{\\log_2 D-0.45}', 900, 395, { size: 28, alpha: a4 });
      const a5 = b.on(5);
      D.card(90, 590, 1100, 100, { alpha: a5, stroke: C.orange });
      c.text('string isomorphism only, not graphs.  Floor is an artefact of "branch, recurse, never memoize":', 640, 620, { size: 20, alpha: a5 });
      c.text('this same family is fixed-parameter tractable by memoizing over block pairs.', 640, 660, { size: 20, alpha: a5 });
    },
  });

  // Status card
  V.scene({
    post: 1.0,
    beats: [
      { say: 'And now, plainly, the status of that bound. Please read this card. It is not in the Hajiaghayi and JafariRaviz paper. It came out of this project. It is conditional on their analysis being correct. It passed one AI verification and one AI red-team review, and has not been checked by a human. The re-accounting with Lambda is not machine-checked. Only their original theorem is, in Lean, modulo ten cited axioms. The best published bound remains n to the polylog of d.', hold: 2.0 },
    ],
    draw(c_, b) {
      const a = b.on(0);
      D.card(80, 90, 1120, 540, { alpha: a, stroke: C.red, lw: 2.5 });
      c.text('Status of the degree-d bound', 640, 142, { size: 34, weight: 700, alpha: a });
      const items = [
        'NOT in the Hajiaghayi–JafariRaviz paper; it came out of this project.',
        'CONDITIONAL on HJ\'s analysis being correct.',
        'Passed one AI verification and one AI red-team review.',
        'NOT checked by a human.',
        'The Λ re-accounting is NOT machine-checked.',
        'Only HJ\'s original theorem is: Lean, modulo 10 cited axioms.',
      ];
      items.forEach((t, i) => c.text('•  ' + t, 150, 215 + i * 48, { size: 24, align: 'left', alpha: a, weight: i === 4 ? 700 : 450 }));
      c.tex('\\text{Published best:\\quad} n^{\\mathrm{polylog}\\,d}\\ \\ (\\text{Grohe, Neuen, Schweitzer})', 640, 548, { size: 28, alpha: a });
    },
  });
})();
