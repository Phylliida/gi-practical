/* Chapter 6: Luks's recursion and the wall. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr; const DATA = window.DATA;
  V.chapter('luks', "Luks's recursion, and the wall");
  const hx = DATA.hexagon, run = DATA.luks_run;
  const hexPos = (cx, cy, R) => D.circle(6, cx, cy, R, -Math.PI / 2);
  const colOf = (ch) => (ch === 'R' ? C.orange : C.blue);
  // Coset structure on the antipodal blocks, computed exactly from the 12 elements.
  const blocksOf = (p) => [p[0] % 3, p[1] % 3, p[2] % 3].join('');
  const classes = {};
  hx.elements.forEach((g) => { (classes[blocksOf(g)] = classes[blocksOf(g)] || []).push(g); });
  const reps = Object.values(classes).map((els) => els[0]);
  function branchResult(g) {
    // positions i and i+3 form block i. Compare colours of x on each block with y on the image block.
    const x = run.x, y = run.y;
    const res = [];
    for (let bl = 0; bl < 3; bl++) {
      const dom = [bl, bl + 3];
      const a = dom.map((i) => x[i]).sort().join('');
      const c2 = dom.map((i) => y[g[i]]).sort().join('');
      res.push(a === c2);
    }
    return res;
  }
  V.scene({
    beats: [
      'Eugene Luks turned this into a recursion in 1982, and it settles graphs of bounded degree in polynomial time. It has three moves.',
      'Move one. If the group has several orbits, split them. Solve the first orbit. What comes back is the whole set of compatible rearrangements. Restrict to that set, and solve the next orbit. This is the chain rule.',
      'Notice why the answer has to be complete. If the first step returned a single example, the next orbit might have no compatible continuation, and we would wrongly conclude no.',
      'Move two. If the group is transitive, take a block system whose quotient is primitive, say on d blocks. Now enumerate every way the group can permute those blocks.',
      'For each way, the rest of the group fixes every block, so the problem falls apart into d separate problems, one per block, each on s over d positions.',
      'Here it is on a real pair of strings on the hexagon. Six ways to permute the three opposite pairs. For each, compare the colours block by block. Five fail. One survives, and it is a rotation by one step.',
      'Move three is the recursion: do the same inside each surviving piece, all the way down.',
    ],
    draw(c_, b) {
      D.title('The three moves', { alpha: b.on(0) });
      // Strings on the hexagon
      const A = hexPos(250, 262, 105), B = hexPos(250, 542, 105);
      const a = b.on(0);
      const edges = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]];
      const drawS = (P, s, alpha, lab) => {
        D.graph(P, edges, { r: 17, fill: (i) => colOf(s[i]), alpha, labels: (i) => i, labelSize: 16, labelFill: '#111' });
        c.tex(lab, P[0][0], (P[0][1] + P[3][1]) / 2, { size: 26, alpha });
      };
      drawS(A, run.x, a, 'x'); drawS(B, run.y, a, 'y');
      // right: labels for moves
      const pnl = (y, title, sub, al, col) => {
        c.circle(525, y, 10, { fill: col || C.ink2, alpha: al });
        c.text(title, 545, y, { size: 23, weight: 600, align: 'left', alpha: al });
        if (sub) c.text(sub, 545, y + 32, { size: 19, fill: C.ink2, align: 'left', alpha: al });
      };
      pnl(120, 'Orbits: the chain rule', 'keep every compatible answer, then continue', b.on(1), C.aqua);
      pnl(205, 'Blocks: enumerate the quotient', 'one branch per way of permuting the d blocks', b.on(3), C.orange);
      pnl(290, 'Recurse inside the blocks', 'each piece has s/d positions', b.on(4), C.violet);
      // branch diagram from beat 5
      const al2 = b.on(5);
      if (al2 > 0) {
        c.text('6 branches on this real instance:', 545, 365, { size: 21, align: 'left', alpha: al2, weight: 500 });
        reps.forEach((g, i) => {
          const res = branchResult(g);
          const y = 402 + i * 36; const ok = res.every(Boolean);
          const rev = D.ease(Math.min(1, ((b.t - b.s(5)) / b.d(5) - 0.05 - i * 0.1) / 0.15));
          c.text('branch ' + (i + 1), 545, y, { size: 19, align: 'left', fill: C.ink2, alpha: al2 });
          for (let j = 0; j < 3; j++) {
            c.circle(660 + j * 34, y, 11, { fill: res[j] ? C.green : C.red, alpha: al2 * rev });
            c.text(res[j] ? '=' : '≠', 660 + j * 34, y + 0.5, { size: 15, fill: '#fff', weight: 700, alpha: al2 * rev });
          }
          c.text(ok ? 'survives' : 'dies', 790, y, { size: 19, weight: ok ? 650 : 400, align: 'left', fill: ok ? C.ink : C.ink3, alpha: al2 * rev });
        });
      }
    },
  });

  V.scene({
    beats: [
      'Each level multiplies by the size of the quotient, and divides the positions by d. If P is the primitive quotient, the recurrence says the work on s positions is at most the size of P, times d, times the work on s over d positions.',
      'If P is polynomially small in d, this recursion is polynomial. That is Luks.',
      'But look what happens when P is everything. If the quotient is the full symmetric group on d blocks, there are d factorial branches. And d can be almost as large as s.',
      'How often can this happen? Thanks to the classification of finite simple groups, we know exactly. Cameron, sharpened by Maróti: a primitive group of degree d is either small, with order below d to the power 1 plus log base 2 of d, or it is built from a big alternating group acting on subsets of some set of m labels.',
      'Small groups can simply be enumerated, at a price of d to the log d. Already quasi-polynomial. The second case is the wall. Babai calls it the Luks barrier: either the recursion goes through, or we find ourselves staring at a giant.',
    ],
    draw(c_, b) {
      D.title('The recurrence, and the wall', { alpha: b.on(0) });
      c.tex('T(s)\\,\\le\\, |P|\\cdot d\\cdot T(s/d)', 640, 112, { size: 32, alpha: b.on(0) });
      // Fans: |P| small vs giant
      const tree = (cx, branches, alpha, col, y) => {
        for (let i = 0; i < branches; i++) {
          const t2 = branches === 1 ? 0.5 : i / (branches - 1);
          const xx = cx - 170 + 340 * t2;
          c.line(cx, y, xx, y + 150, { stroke: col, lw: branches > 30 ? 0.8 : 2, alpha: alpha * (branches > 30 ? 0.5 : 0.9) });
        }
        c.circle(cx, y, 9, { fill: C.bg3, stroke: C.ink2, alpha });
      };
      const a1 = b.on(1), a2 = b.on(2);
      tree(330, 6, a1, C.aqua, 200);
      c.tex('|P|\\ \\text{small}', 330, 386, { size: 26, alpha: a1 });
      c.tex('T(s) = s^{O(1)}', 330, 426, { size: 26, alpha: a1 });
      tree(950, 90, a2, C.red, 200);
      c.tex('|P| = d!', 950, 386, { size: 26, alpha: a2 });
      c.text('branching explodes', 950, 426, { size: 22, alpha: a2, fill: C.ink });
      const a3 = b.on(3);
      c.rect(100, 475, 1080, 200, { fill: C.bg2, stroke: C.rule, lw: 1.2, r: 10, alpha: a3 });
      c.text('primitive group of degree d ≥ 25 (Cameron, Maróti, via the classification)', 640, 505, { size: 22, weight: 600, alpha: a3 });
      c.text('order below', 215, 560, { size: 22, align: 'left', alpha: a3 });
      c.tex('d^{1+\\lfloor\\log_2 d\\rfloor}', 415, 560, { size: 26, alpha: a3 });
      c.text('or', 640, 590, { size: 24, weight: 600, fill: C.ink2, alpha: a3 });
      c.text('a giant Alt(m) acting on subsets', 215, 615, { size: 22, align: 'left', alpha: a3 });
      c.text('of m labels, in a product', 215, 645, { size: 22, align: 'left', alpha: a3 });
      const a4 = b.on(4);
      c.text('enumerate:', 760, 560, { size: 22, align: 'left', fill: C.ink2, alpha: a4 });
      c.tex('d^{O(\\log d)}', 910, 560, { size: 26, alpha: a4, align: 'left' });
      c.text('the Luks barrier', 760, 630, { size: 26, weight: 650, align: 'left', alpha: a4 });
    },
  });

  // labels vs positions on Petersen, with real label action.
  const labs = DATA.petersen.labels; // positions: array of [a,b]
  const idxOf = (a, b) => labs.findIndex((p) => (p[0] === a && p[1] === b) || (p[0] === b && p[1] === a));
  V.scene({
    beats: [
      'Here is the model case of a giant, and it is our 10-vertex graph again. Name each vertex by a pair taken from five labels: 1 and 2, 3 and 4, and so on.',
      'Two vertices are joined exactly when their pairs are disjoint. That rule mentions only labels. So a permutation of the five labels moves the ten vertices, and every symmetry of the graph comes this way.',
      'Watch the three-cycle on labels 1, 2 and 3. The labels rotate, and each vertex slides to the vertex named by its new pair. Ten positions move, but the group lives on five labels.',
      'Babai calls this set of labels the ideal domain, and labels the slide in his talks "Plato". In our language: positions in blue, called Omega, where colours are stored, and labels in yellow, called Gamma. Different sets. Keeping them apart is the hard part.',
      'The trouble: enumerating the group means something like m factorial choices. We cannot afford that, and we can\'t cut the group down with blocks, because it is primitive. We need something cleverer, and that was Babai.',
    ],
    draw(c_, b) {
      D.title('Positions and labels', { alpha: b.on(0) });
      const Pv = D.petersenPos(380, 400, 195);
      const a = b.on(0);
      // label ring top
      const Lab = D.circle(5, 980, 300, 130, -Math.PI / 2);
      const g = { 1: 2, 2: 3, 3: 1, 4: 4, 5: 5 };
      const u = b.in(2) ? b.p(2, 0.15, 0.85) : (b.t >= b.s(3) ? 1 : 0);
      const cur = (v) => {
        const [x, y] = labs[v];
        const tgt = idxOf(g[x], g[y]);
        return [lerp(Pv[v][0], Pv[tgt][0], u), lerp(Pv[v][1], Pv[tgt][1], u)];
      };
      D.graph(Pv, DATA.petersen.edges, { r: 0, fill: 'transparent', alpha: a * 0.35, nodeAlpha: 0 });
      Pv.forEach((p, v) => {
        const q = cur(v);
        c.circle(q[0], q[1], 22, { fill: C.pos, alpha: a });
        c.text(labs[v][0] + '' + labs[v][1], q[0], q[1] + 0.5, { size: 16, weight: 700, fill: '#111', alpha: a });
      });
      c.text('positions Ω: ten of them', 380, 648, { size: 22, alpha: a });
      Lab.forEach((p, i) => {
        const lab = i + 1;
        const tgt = g[lab] - 1;
        const qx = lerp(p[0], Lab[tgt][0], u), qy = lerp(p[1], Lab[tgt][1], u);
        c.circle(qx, qy, 26, { fill: C.lab, alpha: a });
        c.text(String(lab), qx, qy + 0.5, { size: 22, weight: 700, fill: '#111', alpha: a });
      });
      c.text('labels Γ: five of them', 980, 490, { size: 22, alpha: a });
      if (b.in(2, 3)) c.text('(1 2 3) on the labels', 980, 540, { size: 22, weight: 600, alpha: b.on(2, 3) });
      if (b.in(3)) { c.tex('G \\twoheadrightarrow \\mathrm{Alt}(\\Gamma)', 980, 540, { size: 30, alpha: b.on(3) }); c.text('Babai: the "ideal domain"', 980, 584, { size: 20, fill: C.ink2, alpha: b.on(3) }); }
      if (b.in(4)) c.tex('|\\mathrm{Alt}(\\Gamma)| = m!/2\\ \\text{ too many to enumerate}', 980, 640, { size: 23, alpha: b.on(4) });
    },
  });
})();
