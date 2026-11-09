/* Chapter 16: a wallet called Phi. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.part('Part V: the bill');
  V.chapter('wallet', 'A wallet called Φ');
  V.scene({
    beats: [
      'Now we derive the running time, on screen, from the start. First, a recurrence that looks harmless: T of s is at most s to the a, times T of s over 2.',
      'Polynomial branching, and the domain halves every time. Your instinct might say polynomial. Unwind it. The factors are s to the a, then s over 2 to the a, then s over 4, and so on, about log s of them.',
      'Multiply them, and the exponents add. That gives a times log s times log s, over 2: e to the order log squared s. A quasi-polynomial, even though nothing looks expensive.',
      'This is the first lesson of the bill. Cost multiplies along a path. So log of cost adds along a path. Log squared is number of levels times log of branching, and each of those is log n.',
      'Our recursion has five resources, not one, and sometimes the domain does not shrink at all. So instead of solving a recurrence, we use a single number that falls with every expensive step. A potential.',
    ],
    draw(c_, b) {
      D.title('Why polynomial branching is not polynomial', { alpha: b.on(0) });
      c.tex('T(s)\\le s^{a}\\,T(s/2)', 640, 110, { size: 36, alpha: b.on(0) });
      // Bars of width log(s/2^i)
      const X0 = 200, Y0 = 560, unit = 26, H = 34;
      const rows = 14;
      const a1 = b.on(1);
      const prog = b.in(1) ? b.p(1, 0.15, 0.95) : (b.t >= b.s(2) ? 1 : 0);
      for (let i = 0; i < rows; i++) {
        const al = D.ease(Math.min(1, prog * rows - i));
        const w = (rows - i) * unit;
        c.rect(X0, Y0 - (i + 1) * H, w, H - 4, { fill: C.blue, alpha: a1 * al * 0.8, r: 2 });
        if (i < 3) c.tex('s/2^{' + i + '}', X0 - 50, Y0 - (i + 0.5) * H, { size: 18, alpha: a1 * al, fill: C.ink2, key: 'sr' + i });
      }
      c.text('log(s/2ⁱ) bits of branching', X0, Y0 + 26, { size: 19, align: 'left', fill: C.ink2, alpha: a1 });
      c.tex('\\log T = a\\sum_{i}\\log\\frac{s}{2^i}\\approx\\frac a2\\log^2 s', 900, 400, { size: 28, alpha: b.on(2) });
      c.tex('T(s)=e^{O(\\log^2 s)}', 900, 468, { size: 36, alpha: b.on(2) });
      const a3 = b.on(3);
      c.text('levels × log(branching)', 900, 275, { size: 26, weight: 650, alpha: a3 });
      c.text('log cost adds along a path', 900, 315, { size: 20, fill: C.ink2, alpha: a3 });
      c.text('Five resources, one number: a potential', 640, 640, { size: 28, weight: 650, alpha: b.on(4) });
    },
  });

  V.scene({
    beats: [
      'Define the weight of a state: W equals s plus 2, to the power D, times e to the Phi. Phi is the potential. D and all the capital letters are fixed constants.',
      'Claim: the total cost below a state is at most K sub N times W. K sub N is the cost of the phase\'s leaves, one fresh call on N to the gamma positions, times a small factor. We prove the claim by induction over the recursion tree.',
      'At a node, the cost is its own work, at most N to the a, plus the costs of its children. If a child has potential lower by delta Phi, then its weight is e to the minus delta Phi, times the parent\'s, up to the prefactor.',
      'Group the children into classes, and suppose a class has M branches. Its total weight is at most M e to the minus delta Phi, times W. For the induction to close, we need that to be at most W over 8J, where J is the number of classes. In the paper J equals 8.',
      'Here is the whole deal, in one line. Multiplying the work by M must be paid for by a potential drop of log M, plus a small constant. Branching costs log M out of the wallet.',
      'One more detail makes it clean. Children inside a single branch live on disjoint domains, so their prefactors, s j plus 2 to the D, add up to at most the parent\'s. That is what lets many small children share one branch for free.',
      'And the node\'s own work, polynomial in N, is paid for by the prefactor: W is at least 2 N to the a, because s is more than N to the gamma, and D is large. So all the children together take at most half of W, the node\'s work takes at most the other half. That closes the induction.',
    ],
    draw(c_, b) {
      D.title('The weighted induction', { alpha: b.on(0) });
      c.tex('W(\\mathcal S)=(s+2)^D\\,e^{\\Phi(\\mathcal S)}', 640, 110, { size: 34, alpha: b.on(0) });
      const a1 = b.on(1);
      c.tex('T(\\mathcal S)\\le K_N\\,W(\\mathcal S)', 640, 168, { size: 30, alpha: a1 });
      // parent bar with children
      const a2 = b.on(2);
      const px = 200, pw = 880, py = 250, ph = 44;
      c.rect(px, py, pw, ph, { fill: C.violet, r: 4, alpha: a2 * 0.9 });
      c.tex('W(\\mathcal S)', px + pw / 2, py + ph / 2, { size: 22, fill: '#fff', alpha: a2 });
      // M children
      const fills = 5;
      const cw = (pw - 24) / fills;
      const a3 = b.on(3);
      for (let i = 0; i < fills; i++) {
        const x = px + i * (cw + 6);
        c.line(px + pw / 2, py + ph, x + cw / 2, 368, { stroke: C.ink3, lw: 1.5, alpha: a2 });
        const h = 34;
        c.rect(x, 368, cw * 0.9, h, { fill: C.blue, r: 3, alpha: a2 * 0.75 });
        c.tex('e^{-\\Delta\\Phi}W', x + cw * 0.45, 368 + h / 2, { size: 16, fill: '#fff', alpha: a2 });
      }
      const a4 = b.on(4);
      c.tex('M\\,e^{-\\Delta\\Phi}\\le\\frac{1}{8J},\\quad\\text{i.e.}\\quad \\Delta\\Phi\\ge\\log M+\\log(8J)', 640, 490, { size: 28, alpha: Math.max(a4, b.on(3)) });
      c.text('branching costs log M out of the wallet', 640, 540, { size: 25, weight: 650, alpha: a4 });
      const a5 = b.on(5), a6 = b.on(6);
      c.tex('\\sum_i(s_i+2)^D\\le(s+2)^D', 330, 630, { size: 24, alpha: a5 });
      c.text('disjoint domains share a branch', 330, 666, { size: 18, fill: C.ink2, alpha: a5 });
      c.tex('\\sum_j W_j\\le\\tfrac12 W,\\quad W\\ge2N^a', 930, 630, { size: 24, alpha: a6 });
      c.text('children plus node toll fit inside W', 930, 666, { size: 18, fill: C.ink2, alpha: a6 });
    },
  });
})();
