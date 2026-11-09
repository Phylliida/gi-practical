/* Chapter 7: Babai's local certificates. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr; const DATA = window.DATA;
  V.part('Part III: Babai');
  V.chapter('babai', 'Local certificates');
  const W = DATA.window;
  const q = W.q;

  // cell geometry for the triangular table of label pairs
  function pairCell(x0, y0, cell, a, b) { return [x0 + (b - 2) * cell, y0 + (a - 1) * cell]; }
  function drawLabelsFrame(x0, y0, cell, T, alpha) {
    for (let v = 2; v <= q; v++) {
      c.circle(x0 + (v - 2) * cell + cell / 2 - 1, y0 - 22, 13, { fill: T.includes(v) ? C.lab : C.bg3, stroke: C.ink3, lw: 1.5, alpha });
      c.text(String(v), x0 + (v - 2) * cell + cell / 2 - 1, y0 - 21.5, { size: 15, weight: 600, fill: T.includes(v) ? '#111' : C.ink, alpha });
    }
    for (let v = 1; v < q; v++) {
      c.circle(x0 - 22, y0 + (v - 1) * cell + cell / 2 - 1, 13, { fill: T.includes(v) ? C.lab : C.bg3, stroke: C.ink3, lw: 1.5, alpha });
      c.text(String(v), x0 - 22, y0 + (v - 1) * cell + cell / 2 - 0.5, { size: 15, weight: 600, fill: T.includes(v) ? '#111' : C.ink, alpha });
    }
  }
  function drawCells(x0, y0, cell, opts, alpha) {
    W.pairs.forEach(([a, b], i) => {
      const [X, Y] = pairCell(x0, y0, cell, a, b);
      let f = W.x[i] ? C.orange : C.blue;
      c.rect(X, Y, cell - 3, cell - 3, { fill: f, r: 3, alpha: alpha * (opts.dim ? (opts.win.has(i) ? 1 : 0.28) : 1) });
      if (opts.win && opts.win.has(i)) c.rect(X, Y, cell - 3, cell - 3, { stroke: C.ink, lw: 2.2, r: 3, alpha });
    });
  }

  V.scene({
    beats: [
      'Babai\'s move is to stop trying to enumerate the giant, and ask a different question: is the giant really there, in this instance?',
      'Two outcomes, and each one is progress. Maybe the symmetry is genuine: automorphisms of the colouring really do realize the giant, on all or nearly all of the labels. Then an efficient Luks reduction peels the giant off, and we recurse on smaller pieces.',
      'Or the symmetry is broken, and then the colouring must be hiding some structure on the labels, a colouring or a partition, that an isomorphism has to respect. Then the giant can be cut down.',
      'Confirm the giant, or break it. Everything else in the algorithm is engineering in service of those two outcomes.',
    ],
    draw(c_, b) {
      D.title('Confirm the giant, or break it', { alpha: b.on(0) });
      const a0 = b.on(0);
      c.tex('G\\twoheadrightarrow\\mathrm{Alt}(\\Gamma),\\quad |\\Gamma|=m', 640, 150, { size: 32, alpha: a0 });
      const a1 = b.on(1), a2 = b.on(2);
      D.card(120, 240, 480, 300, { alpha: a1, stroke: C.green });
      c.text('Confirm', 360, 290, { size: 28, weight: 650, alpha: a1 });
      c.tex('\\mathrm{Aut}_G(x)\\twoheadrightarrow\\mathrm{Alt}(\\Gamma)', 360, 360, { size: 26, alpha: a1 });
      c.text('or at least a giant on 90% of Γ', 360, 415, { size: 19, fill: C.ink2, alpha: a1 });
      c.text('so an efficient Luks reduction peels it off', 360, 460, { size: 19, fill: C.ink2, alpha: a1 });
      D.card(680, 240, 480, 300, { alpha: a2, stroke: C.red });
      c.text('Break', 920, 290, { size: 28, weight: 650, alpha: a2 });
      c.text('a colouring or partition on Γ', 920, 360, { size: 21, alpha: a2 });
      c.text('that every isomorphism must respect', 920, 395, { size: 21, alpha: a2 });
      c.text('then the giant cannot act on Γ', 920, 450, { size: 19, fill: C.ink2, alpha: a2 });
      c.text('that is progress on the bill', 920, 485, { size: 19, fill: C.ink2, alpha: a2 });
      c.text('either way, progress', 640, 590, { size: 24, weight: 600, alpha: b.on(3) });
    },
  });

  const runFull = W.runs.find((r) => r.outcome === 'full' && r.T[0] === 1 && r.T[1] === 2);
  const runNon = W.runs.find((r) => r.outcome === 'nonfull' && r.T[0] === 1);
  V.scene({
    beats: [
      'How do you ask? Locally. Pick a small test set T of labels, and ask a small question. Can the colour-preserving rearrangements still realize every even permutation of T?',
      'Here is a real instance. Seven labels, so 21 positions, one for each pair of labels, with a real two-colouring. The test set has three labels.',
      'Start from all relabelings that preserve T, with nothing checked yet. Now grow a window of checked positions.',
      'First, find the positions the test can see: those where fixing the position changes which even permutations of T remain possible. Call them affected.',
      'Check the colours on those positions, and keep only the relabelings that respect them. Those positions join the window. That one step is a recursive call on the group that fixes T pointwise, whose orbits inside an affected orbit are at most a 1 over k fraction of it.',
      'Now look at the two possible endings, using the same colouring and two different test sets.',
      'Test set 1, 2, 4: nothing else is affected, and the relabelings fixing everything outside the window still realize all even permutations of T. This is a full certificate: actual automorphisms of the whole string.',
      'Test set 1, 2, 3: after the window grows, the remaining relabelings can no longer realize all even permutations of T. Non-full. And that failure is itself information: it depends only on the colouring, so it is shared by every isomorphism.',
    ],
    draw(c_, b) {
      D.title('Local certificates', { alpha: b.on(0) });
      const x0 = 96, y0 = 150, cell = 56;
      const a = b.on(1);
      // pick which run to display: full run first, then non-full for last beat
      const showFull = b.in(5) && b.t < b.s(7);
      const useRun = b.t >= b.s(7) ? runNon : runFull;
      const T = useRun.T;
      const log = useRun.log;
      const first = log[0];
      let win = new Set();
      const step1 = b.p(4, 0.1, 0.45);
      if (b.t >= b.s(4) + 0.45 * b.d(4) * step1 && b.in(4)) { win = new Set(first.added); }
      if (b.t >= b.e(4) - 0.2) { win = new Set(first.added); }
      drawCells(x0, y0, cell, { win, dim: win.size > 0 }, a);
      drawLabelsFrame(x0, y0, cell, T, a);
      if (b.in(1, 5)) D.simplified(420, 150 + cell * 6 + 22, b.on(1, 5), 'real algorithm: test sets are much larger');
      c.text('a real string on 21 positions', 96, 150 + cell * 6 + 52, { size: 18, fill: C.ink2, align: 'left', alpha: a });
      // the right column: state
      const R = 760;
      c.tex('T = \\{' + T.join(',') + '\\}', R, 130, { size: 30, alpha: b.on(0), fill: C.ink, key: 'T' });
      const ab = b.on(2);
      c.text('relabelings still possible:', R, 195, { size: 20, fill: C.ink2, align: 'left', alpha: ab });
      const shownA = b.in(4) ? (b.p(4, 0.55, 0.95) > 0.5 ? first.after : first.A) : (b.in(5) || b.in(6) || b.in(7) ? (log[1].A ?? first.after) : first.A);
      c.text(String(shownA), R, 232, { size: 34, weight: 650, align: 'left', alpha: ab });
      c.text('window: ' + win.size + ' of 21 positions', R, 280, { size: 20, fill: C.ink2, align: 'left', alpha: ab });
      // explanations
      const a3 = b.on(3, 5);
      c.tex('\\text{affected: } \\phi_T(A_v)\\neq\\mathrm{Alt}(T)', R, 345, { size: 25, alpha: a3 });
      if (b.in(4, 5)) c.text('recursive call on orbits of at most s/k positions', R, 395, { size: 20, fill: C.ink2, alpha: b.on(4, 5) });
      if (b.in(6, 7)) {
        const a4 = b.on(6, 7);
        D.card(R - 200, 340, 400, 200, { alpha: a4, stroke: C.green });
        c.text('Full certificate', R, 375, { size: 26, weight: 650, alpha: a4 });
        c.text('K = ' + log[1].K + ' relabelings fix the rest', R, 420, { size: 20, alpha: a4 });
        c.text('and realize all of Alt(T):', R, 450, { size: 20, alpha: a4 });
        c.text('real automorphisms of x', R, 495, { size: 21, weight: 600, alpha: a4 });
      }
      if (b.in(7)) {
        const a5 = b.on(7);
        D.card(R - 200, 340, 400, 200, { alpha: a5, stroke: C.red });
        c.text('Non-full', R, 375, { size: 26, weight: 650, alpha: a5 });
        c.text('image of remaining group on T', R, 420, { size: 20, alpha: a5 });
        c.text('is a proper subgroup of Alt(T)', R, 450, { size: 20, alpha: a5 });
        c.text('equivariant: reused by every isomorphism', R, 495, { size: 19, fill: C.ink2, alpha: a5 });
      }
    },
  });

  // Why k ~ log n
  V.scene({
    beats: [
      { say: 'So why did Babai make k about log n? Before I answer, let me ask you. A smaller test set means fewer test sets. Why not use k equals 3?', hold: 1.2 },
      'The danger is the ending we called full. When no position is affected, we want to conclude that the relabelings fixing everything outside the window still realize all of Alt(T). Babai\'s Unaffected Stabilizer Theorem says exactly that, but only when k is above a threshold: greater than 8 and greater than 2 plus log base 2 of n.',
      'Below the threshold, it can genuinely fail, and here is the cleanest picture of how. Take the alternating group on k points, and let it act on itself, by multiplying from the left and from the right at the same time. That is a transitive group on k factorial over 2 positions.',
      'The left half is a copy of Alt(k), our test. But the right half, on its own, already reaches every position. So whatever even permutation the test makes, the right half can bring a given position back: fixing a position puts no limit on the test. Every position is unaffected. Yet no relabeling fixes all positions and still moves the labels. So the procedure has nothing to check and no real automorphism to report. It is stuck.',
      'Here k is only about log n over log log n. In his talks Babai notes the threshold is tight, with infinitely many examples at the boundary. A constant-size test set is exactly the regime where this happens.',
      'So Babai needs test sets of size about log n. And that is one logarithm on our bill.',
    ],
    draw(c_, b) {
      D.title('Why test sets had to be big', { alpha: b.on(0) });
      const a = b.on(0);
      c.tex('k > \\max\\{8,\\ 2+\\log_2 n\\}', 640, 120, { size: 30, alpha: b.on(1) });
      c.text('Unaffected Stabilizer Theorem', 640, 158, { size: 20, fill: C.ink2, alpha: b.on(1) });
      // Grid picture: Alt(k) acting on itself by left and right multiplication
      const ax = b.on(2);
      const cx = 400, cy = 440, s = 44, n = 7;
      for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
        c.rect(cx - (n / 2) * s + i * s, cy - (n / 2) * s + j * s, s - 5, s - 5, { fill: C.pos, r: 3, alpha: ax * (0.45 + 0.2 * ((i + j) % 2)) });
      }
      c.text('cartoon grid: positions = Alt(k), left ⟷ right', cx, 668, { size: 19, fill: C.ink2, alpha: ax });
      const al = b.on(3);
      if (al > 0) {
        c.arrow(cx - 3.5 * s, cy - 3.5 * s - 32, cx + 3.5 * s, cy - 3.5 * s - 32, { stroke: C.lab, lw: 4, alpha: al });
        c.text('the test (left Alt(k))', cx, cy - 3.5 * s - 56, { size: 20, fill: C.ink, alpha: al });
        c.arrow(cx + 3.5 * s + 32, cy + 3.5 * s, cx + 3.5 * s + 32, cy - 3.5 * s, { stroke: C.violet, lw: 4, alpha: al });
        c.text('right Alt(k)', cx + 3.5 * s + 44, cy, { size: 20, fill: C.ink, align: 'left', alpha: al });
        c.text('transitive already', cx + 3.5 * s + 44, cy + 26, { size: 18, fill: C.ink2, align: 'left', alpha: al });
      }
      const ar = b.on(3);
      D.card(760, 280, 410, 200, { alpha: ar });
      c.text('Fixing every test label', 965, 320, { size: 22, weight: 600, alpha: ar });
      c.text('leaves the orbit unchanged', 965, 352, { size: 22, weight: 600, alpha: ar });
      c.text('every position unaffected,', 965, 396, { size: 19, fill: C.ink2, alpha: ar });
      c.text('no progress, no automorphism', 965, 424, { size: 19, fill: C.ink2, alpha: ar });
      const a4 = b.on(4);
      c.tex('k \\approx \\log n/\\log\\log n', 965, 530, { size: 26, alpha: a4 });
      c.text('Babai: threshold is tight', 965, 568, { size: 20, fill: C.ink2, alpha: a4 });
      D.bill(240, 96, [{ color: C.violet, alpha: b.on(5) }, { color: C.rule, tex: '?', alpha: b.on(5) * 0.45 }, { color: C.rule, tex: '?', alpha: b.on(5) * 0.45 }], { w: 74, h: 38, size: 18, gap: 8 });
    },
  });

  V.scene({
    beats: [
      'We run the test on every k-subset of the labels, in all pairs of orderings, and then aggregate. All the full certificates together generate a group of real automorphisms.',
      'If those certificates cover enough of the giant, we have confirmed it and we peel it off. If they do not, the pattern of which tests were full or non-full turns into a coloured structure on k-tuples of labels.',
      'Babai then runs the Design Lemma to reduce that structure to a coloured graph on the labels, and then a procedure called Split-or-Johnson to extract a real colouring or partition of the labels from the graph. I will treat those as black boxes for now and open them only where it matters for the running time.',
      'Babai\'s recursion, then, reduces the giant on labels, or shrinks the positions. It works. The question is what it costs.',
    ],
    draw(c_, b) {
      D.title('Aggregating the tests', { alpha: b.on(0) });
      const a = b.on(0);
      // tiles of tests
      const rows = 7, cols = 5;
      let k = 0;
      for (let j = 0; j < rows; j++) for (let i = 0; i < cols; i++) {
        const r = W.runs[k % W.runs.length]; k++;
        c.rect(120 + i * 44, 130 + j * 44, 38, 38, { fill: r.outcome === 'full' ? C.green : C.red, r: 5, alpha: a * 0.85 });
        c.text(r.outcome === 'full' ? 'F' : 'N', 120 + i * 44 + 19, 130 + j * 44 + 19.5, { size: 17, weight: 700, fill: '#fff', alpha: a * 0.85 });
      }
      c.text('all 35 three-label tests, real outcomes', 220, 455, { size: 18, fill: C.ink2, alpha: a });
      const a1 = b.on(1);
      D.card(420, 150, 390, 360, { alpha: a1 });
      c.text('Full certificates', 615, 186, { size: 24, weight: 600, alpha: a1 });
      c.tex('F = \\langle K(T)\\rangle \\le \\mathrm{Aut}_G(x)', 615, 245, { size: 24, alpha: a1 });
      c.text('confirm: giant on most of Γ', 615, 300, { size: 20, fill: C.ink2, alpha: a1 });
      c.text('peel it off, recurse on the kernel', 615, 330, { size: 20, fill: C.ink2, alpha: a1 });
      c.text('or: a k-ary structure on Γ', 615, 395, { size: 20, fill: C.ink2, alpha: a1 });
      c.text('colours come from comparing tests', 615, 425, { size: 20, fill: C.ink2, alpha: a1 });
      const a2 = b.on(2);
      D.card(850, 150, 340, 360, { alpha: a2 });
      c.text('Design Lemma', 1020, 200, { size: 22, weight: 600, alpha: a2 });
      c.text('k-ary to binary', 1020, 232, { size: 19, fill: C.ink2, alpha: a2 });
      c.arrow(1020, 256, 1020, 296, { stroke: C.ink3, alpha: a2, lw: 2 });
      c.text('Split-or-Johnson', 1020, 325, { size: 22, weight: 600, alpha: a2 });
      c.text('binary to a real partition or a', 1020, 357, { size: 19, fill: C.ink2, alpha: a2 });
      c.text('Johnson scheme on Γ', 1020, 383, { size: 19, fill: C.ink2, alpha: a2 });
      c.arrow(1020, 405, 1020, 445, { stroke: C.ink3, alpha: a2, lw: 2 });
      c.text('giant is cut down', 1020, 475, { size: 21, weight: 600, alpha: a2 });
      D.chip('named here, not derived', 640, 575, { alpha: a2, stroke: C.orange });
      c.text('It works. Now, what does it cost?', 640, 635, { size: 26, weight: 600, alpha: b.on(3) });
    },
  });
})();
