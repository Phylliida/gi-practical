/* Chapter 19: from one phase to n^{O(log n)}. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('recurrence', 'From a phase to n^O(log n)');

  V.scene({
    beats: [
      'So the cost of a whole phase is the cost of its leaves, times W at the root. K sub N is one fresh call on N to the gamma positions, times E sub N, which is e to the c T log squared N, the additive row-terminal work.',
      'W at the root is e to the Phi, with Phi order log squared N. So a phase costs e to the C log squared N, times one recursive call of size N to the gamma.',
      'Write F of N for the worst-case time on N positions. We get the recurrence: F of N is at most e to the C log squared N, times 1 plus F of N to the gamma.',
      'Now you might worry about the number of phases. You might guess each phase costs an extra factor of log. Unwind it and see.',
      { say: 'Each phase raises N to the power gamma, so log N is multiplied by gamma. So log squared N is multiplied by gamma squared. The exponents form a geometric series.', hold: 0.6 },
      'The paper fixes gamma hat, a tiny bit above gamma. The whole sum is at most C log squared N, over 1 minus gamma hat squared. One constant, independent of how many phases there are.',
    ],
    init: () => ({ gam: 0.9, touched: false }),
    buildUI(el, ix, inv, touch) {
      const box = document.createElement('div'); box.className = 'tryit';
      box.style.left = '6%'; box.style.bottom = '7%';
      const lab = document.createElement('span'); lab.textContent = 'Try it: γ̂ =';
      const input = document.createElement('input'); input.type = 'range'; input.min = '0.5'; input.max = '0.99'; input.step = '0.01'; input.value = '0.9';
      const val = document.createElement('b'); val.textContent = '0.90';
      input.oninput = () => { ix.gam = parseFloat(input.value); ix.touched = true; val.textContent = ix.gam.toFixed(2); touch(); };
      box.append(lab, input, val); el.appendChild(box);
    },
    draw(c_, b, ix) {
      D.title('Summing the phases', { alpha: b.on(0) });
      c.tex('\\text{phase cost}=K_N\\,W(\\text{root})\\ \\ ,\\quad K_N=E_N\\,(1+F(\\lceil N^\\gamma\\rceil))', 640, 110, { size: 26, alpha: b.on(0) });
      c.tex('E_N=e^{c_T\\log^2(N+2)}', 640, 150, { size: 22, alpha: b.on(0), fill: C.ink2 });
      c.tex('F(N)\\le e^{C\\log^2(N+2)}\\big(1+F(\\lceil N^\\gamma\\rceil)\\big)', 640, 208, { size: 34, alpha: b.on(2) });
      // Squares
      const a = b.on(3);
      const gam = ix.gam;
      const X0 = 50, Y0 = 590, S = 270;
      let x = X0;
      let total = 0;
      for (let j = 0; j < 12; j++) {
        const side = S * Math.pow(gam, j);
        const appear = b.in(3) ? D.ease(Math.min(1, (b.t - b.s(3)) / (b.d(3) * 0.6) * 12 - j)) : (b.t >= b.s(4) ? 1 : 0);
        const prog = (b.t >= b.s(4) ? 1 : appear);
        c.rect(x, Y0 - side, side, side, { fill: C.x2, alpha: a * prog * 0.72, r: 2 });
        c.rect(x, Y0 - side, side, side, { stroke: C.bg, lw: 1.5, alpha: a * prog });
        if (j < 3) c.tex(j === 0 ? '\\log^2 N' : (j === 1 ? '(\\gamma\\log N)^2' : '(\\gamma^2\\log N)^2'), x + side / 2, Y0 - side / 2, { size: 19, fill: '#fff', alpha: a * prog, key: 'sq' + j });
        x += side + 6;
        total += side * side;
        if (x > 800) break;
      }
      // Sum formula
      const a5 = b.on(5);
      const shown = 1 / (1 - gam * gam);
      c.tex('\\sum_{j\\ge0}\\hat\\gamma^{2j}=\\frac{1}{1-\\hat\\gamma^2}=' + shown.toFixed(2), 1050, 350, { size: 30, alpha: Math.max(a5, b.on(4)) });
      c.tex('F(N)\\le e^{\\frac{C}{1-\\hat\\gamma^2}\\log^2(N+2)}', 1050, 420, { size: 30, alpha: a5 });
      if (b.in(4) && !ix.touched) c.text('(slide γ̂ to change the series)', 1050, 470, { size: 17, fill: C.ink2, alpha: 0.9 });
    },
  });

  V.scene({
    beats: [
      'Now the promise from the very beginning. Graph isomorphism on n vertices is string isomorphism on N equals n squared positions. And it costs nothing, because log squared of n squared is exactly 4 log squared n.',
      'Squaring the input only multiplies the constant in the exponent by 4. Hence the bound, exp of order log squared n, which you can also write as n to the order log n.',
      'So: inside a phase, constant shrinks and polynomial branching give two logs: e to the log squared. Phases shrink polynomially, so the series is geometric, and no third factor can appear. Then the n squared positions change only a constant. That is the whole derivation.',
    ],
    draw(c_, b) {
      D.title('Paying off the worry from chapter 4', { alpha: b.on(0) });
      c.tex('N=n^2', 640, 180, { size: 44, alpha: b.on(0) });
      c.tex('\\log^2(n^2)=(2\\log n)^2=4\\log^2 n', 640, 280, { size: 42, alpha: b.on(0) });
      c.tex('e^{O(\\log^2 n)}=n^{O(\\log n)}', 640, 400, { size: 52, alpha: b.on(1) });
      const a2 = b.on(2);
      const items = ['inside a phase: two logs', 'phases: geometric, no new log', 'N = n²: only a constant'];
      items.forEach((t, i) => { D.chip(t, 240 + i * 400, 560, { alpha: a2, size: 20, stroke: C.blue }); });
    },
  });
})();
