/* Chapter 4: strings and allowed relabelings. */
(function () {
  const { C, c } = V; const D = window.Dr; const DATA = window.DATA;
  V.part('Part II: the language of symmetry');
  V.chapter('strings', 'Strings and allowed relabelings');
  const A = DATA.petersen.A; const N = A.length;
  const SW = [3, 7];
  V.scene({
    beats: [
      'Time to change the question, into one that can be asked about smaller pieces of itself.',
      'Write the graph as a table. One cell for every ordered pair of vertices, coloured by whether that pair is the same vertex twice, an edge, or a non-edge.',
      'Now try a renaming of the vertices. Cells do not move freely. Swap vertices 3 and 7, and row 3 swaps with row 7, and column 3 swaps with column 7, at the same time.',
      'So the table is a string on n squared positions, and a graph isomorphism is one very particular kind of rearrangement of those positions: one that comes from renaming vertices.',
      'Let G be the set of allowed rearrangements. The problem becomes: given two colourings x and y of the positions, find every g in G that turns x into y. Babai likes the Rubik\'s cube picture: can this colouring reach that one by legal moves?',
      'The move from graphs to strings is not a trick for its own sake. It is the Pólya move: when the problem is too rigid to recurse on, find a related problem that is not. Restrict G, or restrict to some of the positions, and you get a smaller instance of the same problem.',
      'You might worry that we just squared the size of the input. Hold that thought. It is going to matter, and it will turn out not to cost what you might expect.',
    ],
    draw(c_, b) {
      D.title('A graph is a string on n² positions', { alpha: b.on(0) });
      const cell = 34, x0 = 130, y0 = 120;
      const u = b.in(2) ? b.p(2, 0.15, 0.85) : 0;
      const [a0, a1] = SW;
      const remap = (i) => { if (b.t < b.s(2) - 0.5) return i; if (i === a0) return a0 + (a1 - a0) * u; if (i === a1) return a1 + (a0 - a1) * u; return i; };
      const alph = b.on(1);
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) {
        const col = i === j ? C.ink3 : A[i][j] ? C.blue : C.bg3;
        const ri = remap(i), rj = remap(j);
        c.rect(x0 + rj * cell, y0 + ri * cell, cell - 3, cell - 3, { fill: col, r: 3, alpha: alph });
      }
      // highlight rows/cols being swapped
      if (b.in(2, 3)) {
        const la = b.on(2, 3);
        [a0, a1].forEach((k) => {
          const rk = remap(k);
          c.rect(x0 + rk * cell - 2, y0 - 2, cell, cell * N + 3, { stroke: C.orange, lw: 2.5, alpha: la, r: 4 });
          c.rect(x0 - 2, y0 + rk * cell - 2, cell * N + 3, cell, { stroke: C.orange, lw: 2.5, alpha: la, r: 4 });
        });
      }
      const fs = 18;
      for (let i = 0; i < N; i++) { c.text(String(i), x0 + i * cell + cell / 2 - 2, y0 - 16, { size: fs, fill: C.ink2, alpha: alph }); c.text(String(i), x0 - 18, y0 + i * cell + cell / 2 - 2, { size: fs, fill: C.ink2, alpha: alph }); }
      // Legend (direct labels)
      const lx = 520, ly = 150;
      [[C.ink3, 'same vertex twice'], [C.blue, 'edge'], [C.bg3, 'non-edge']].forEach(([f, t], i) => {
        c.rect(lx, ly + i * 34, 22, 22, { fill: f, r: 3, alpha: alph }); c.text(t, lx + 34, ly + 11 + i * 34, { size: 20, align: 'left', fill: C.ink2, alpha: alph });
      });
      c.text('n² = 100 positions', lx, ly + 130, { size: 26, weight: 600, align: 'left', alpha: b.on(1) });
      // problem definition panel
      const a2 = b.on(3, 5);
      c.tex('\\Omega = [n]\\times[n],\\quad G \\cong \\mathrm{Sym}(n)', 860, 345, { size: 26, alpha: a2 });
      c.tex('\\text{colourings } x, y:\\Omega\\to\\Sigma', 860, 395, { size: 25, alpha: a2 });
      const a3 = b.on(4);
      c.tex('\\mathrm{Iso}_G(x,y)=\\{\\,g\\in G: x^{g}=y\\,\\}', 860, 475, { size: 30, alpha: a3 });
      c.text('String isomorphism', 860, 438, { size: 22, weight: 600, fill: C.ink2, alpha: a3 });
      // Recursion note
      const a4 = b.on(5);
      c.text('smaller G or fewer positions: same problem again', 860, 528, { size: 22, alpha: a4 });
      // hold-that-thought chip
      if (b.on(6) > 0) D.simplified(860, 590, b.on(6), 'N = n² positions: a worry to revisit');
    },
  });

  // Coset scene: answer is one iso plus generators
  V.scene({
    beats: [
      'What does find every g even mean, if there can be factorially many?',
      'Suppose pi is one isomorphism from x to y, and phi is any symmetry of x, meaning any g with x to the g equals x. Then doing phi and then pi is again an isomorphism. And every isomorphism has this form.',
      'So the whole answer is one isomorphism, plus a list of generators of the symmetry group. For our 10-vertex graph that is 120 symmetries, described by just a handful of permutations.',
      'Group people call this set a coset. For us it is simply the shape every answer will have, and it will turn out to be the most important design decision in the algorithm: every recursive call returns its whole coset, and never just one example.',
    ],
    draw(c_, b) {
      D.title('An answer is a coset', { alpha: b.on(0) });
      const a = b.on(1);
      // left: the cloud of isomorphisms
      const cx = 360, cy = 360;
      const dots = [];
      for (let i = 0; i < 120; i++) { const t = i * 2.399963; const r = 11 * Math.sqrt(i + 1.2); dots.push([cx + r * Math.cos(t), cy + r * 0.7 * Math.sin(t)]); }
      dots.forEach((p, i) => c.circle(p[0], p[1], 4.5, { fill: C.violet, alpha: a * 0.85 }));
      c.tex('\\mathrm{Aut}_G(x)\\,\\pi', cx, 590, { size: 30, alpha: a });
      c.text('every element is a valid isomorphism', cx, 630, { size: 20, fill: C.ink2, alpha: a });
      // right: compact description
      const a2 = b.on(2);
      c.rect(700, 170, 460, 300, { fill: C.bg2, stroke: C.rule, r: 12, alpha: a2, lw: 1.2 });
      c.text('the answer we return', 930, 208, { size: 24, weight: 600, alpha: a2 });
      c.tex('\\pi', 800, 268, { size: 34, fill: C.orange, alpha: a2 });
      c.text('one isomorphism', 870, 268, { size: 21, align: 'left', alpha: a2 });
      c.text('generators of Aut(x):', 800, 330, { size: 21, alpha: a2, align: 'left' });
      c.text(DATA.petersen.n_gens + ' permutations', 800, 366, { size: 21, weight: 600, alpha: a2, align: 'left' });
      c.text('describe ' + DATA.petersen.aut_order + ' elements', 800, 396, { size: 21, fill: C.ink2, alpha: a2, align: 'left' });
      c.text('Complete answers, everywhere', 640, 520, { size: 26, weight: 650, alpha: b.on(3) });
    },
  });
})();
