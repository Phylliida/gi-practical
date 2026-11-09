/* Chapter 10: the hereditary budget sigma. */
(function () {
  const { C, c } = V; const D = window.Dr;
  V.chapter('sigma', 'The hereditary budget σ');
  V.scene({
    beats: [
      'A chain of groups. Start at G, and go down through subgroups, H zero, H one, and so on.',
      'Sometimes a step is special. Say the step from H i to H i plus one is marked when H i plus one is normal in H i, the quotient is Alt of k, with k at least kappa, the smaller group is still transitive on the current orbit, and the quotient is visible: the part of the group that fixes the whole active orbit lies inside H i plus one.',
      'Sigma of G is the largest total weight of marks that any chain can collect. It is a definition about the group, over all chains. The algorithm never computes it.',
      'Three properties. One: sigma never increases when you restrict to a subgroup, or to one orbit. Because a chain in the smaller group can be lifted, and prefixed by that restriction: it was already a chain in the bigger one.',
      'Two: if the group has a normal subgroup that is still transitive, with a quotient Alt of k and k at least kappa, then sigma drops by at least k when you pass to it. That is just prefixing the chain by one marked step. This is exactly our visible-endpoint step, and it is why it pays.',
      'Three: and this is the theorem: sigma of G is at most C log of the degree, minus B. C and B are absolute constants. The total weight of all the marks along any chain is logarithmic.',
    ],
    draw(c_, b) {
      D.title('The hereditary budget σ', { alpha: b.on(0) });
      const a = b.on(0);
      // the chain, vertical
      const X = 170, Y = [130, 225, 320, 415, 510, 600];
      const names = ['G = H_0', 'H_1', 'H_2', 'H_3', 'H_4', 'H_5'];
      const marked = [false, true, false, true, false];
      Y.forEach((y, i) => {
        c.tex(names[i], X, y, { size: 26, alpha: a });
        if (i < 5) {
          const m = marked[i];
          c.line(X, y + 22, X, Y[i + 1] - 22, { stroke: m ? C.sig : C.ink3, lw: m ? 4 : 2.5, alpha: a });
          if (m) {
            const u = b.on(1);
            c.circle(X - 32, (y + Y[i + 1]) / 2, 13, { fill: C.sig, alpha: u });
            c.tex('k_' + i, X - 72, (y + Y[i + 1]) / 2, { size: 20, fill: C.ink, alpha: u, key: 'km' + i });
          }
        }
      });
      // marked conditions
      const m1 = b.on(1);
      c.text('A marked step, weight k ≥ κ:', 420, 130, { size: 22, weight: 600, align: 'left', alpha: m1 });
      const lines = ['H_{i+1}\\trianglelefteq H_i,\\quad H_i/H_{i+1}\\cong\\mathrm{Alt}(k)', 'H_{i+1}\\text{ transitive on the active orbit }\\Delta_i', '(H_i)_{(\\Delta_i)}\\le H_{i+1}\\quad(\\text{visible})'];
      lines.forEach((l, i) => c.tex(l, 430, 175 + i * 48, { size: 23, align: 'left', alpha: m1 }));
      const m2 = b.on(2);
      c.tex('\\sigma(G,\\Omega)=\\max_{\\text{chains}}\\ \\sum_{\\text{marked } i}k_i', 790, 345, { size: 32, alpha: m2 });
      c.text('analysis only: the algorithm never computes it', 790, 392, { size: 18, fill: C.ink2, alpha: m2 });
      // Properties
      const rows = [
        { y: 440, tex: '\\sigma\\text{ nonincreasing under subgroups and orbit images}', on: 3 },
        { y: 490, tex: '\\sigma(N)\\le\\sigma(G)-k\\ \\text{ for } N\\trianglelefteq G,\\ G/N\\cong\\mathrm{Alt}(k),\\ k\\ge\\kappa,\\ N\\text{ transitive}', on: 4 },
        { y: 540, tex: '\\sigma(G,\\Omega)\\le C\\log n - B', on: 5, big: true },
      ];
      rows.forEach((r, i) => {
        const al = b.on(r.on);
        c.circle(428, r.y, 12, { fill: C.sig, alpha: al });
        c.text(String(i + 1), 428, r.y + 0.5, { size: 15, weight: 700, fill: '#111', alpha: al });
        c.tex(r.tex, 452, r.y, { size: r.big ? 28 : 21, align: 'left', alpha: al, fill: C.ink });
      });
    },
  });

  V.scene({
    beats: [
      'Why should such a bound hold? Two facts do most of the work.',
      'First, logs add. If the group has a block system with b blocks of size a, then sigma of G is at most sigma on the blocks, plus sigma inside a block. Two pieces of sizes a and b; log a plus log b equals log of a b. So a tower of blocks costs nothing extra.',
      'So the induction bottoms out at primitive groups. For most of those, the paper uses the order of the group: each marked step of weight k uses up at least k over 6 of the factors of 3 or of 5 in the group order. For affine, almost-simple, and diagonal primitive groups, the number of those factors is order log of the degree. That is the input from the classification. Product and Johnson actions get their own short arguments.',
      'And giants? While the action is still a natural giant, no step can be marked, because a transitive normal subgroup of a giant is the alternating group itself. Its quotient is at most cyclic of order 2. A chain has to leave the giant by an ordinary restriction first, and then the cases above apply.',
      'Is the bound tight? Yes. Take r copies of Alt kappa, acting on the r-fold product by multiplying from both sides. There are r steps of weight kappa, and log n is r log of kappa factorial over 2. So sigma is on the order of log n, for fixed kappa.',
      'So a recursion path can take only order log n over kappa of these same-domain steps. That is the fact the potential is going to charge against.',
    ],
    draw(c_, b) {
      D.title('Why σ is at most logarithmic', { alpha: b.on(0) });
      const a1 = b.on(1);
      // Block additivity picture: a × b grid
      const x0 = 110, y0 = 130, a2 = 10, b2 = 5, cell = 26;
      for (let i = 0; i < a2; i++) for (let j = 0; j < b2; j++) c.rect(x0 + i * cell + (i % 2) * 3, y0 + j * cell, cell - 3, cell - 3, { fill: j % 2 ? C.aqua : C.blue, r: 2, alpha: a1 * 0.8 });
      c.tex('\\sigma(G)\\le\\sigma(\\text{on blocks})+\\sigma(\\text{inside a block})', 620, 170, { size: 27, align: 'center', alpha: a1 });
      c.tex('\\log a + \\log b = \\log(ab)', 620, 225, { size: 27, alpha: a1, fill: C.sig });
      const a2v = b.on(2);
      D.card(90, 310, 530, 165, { alpha: a2v });
      c.text('affine, almost simple, diagonal:', 110, 345, { size: 21, weight: 600, align: 'left', alpha: a2v });
      c.tex('\\sigma\\le 6\\,v_\\ell(|G|),\\ \\ \\ell\\in\\{3,5\\}', 110, 395, { size: 26, align: 'left', alpha: a2v });
      c.text('v_{ℓ}(|G|) = O(log n), via the classification', 110, 440, { size: 18, align: 'left', fill: C.ink2, alpha: a2v });
      const a3 = b.on(3);
      D.card(660, 310, 530, 165, { alpha: a3 });
      c.text('natural giant Alt(n) or Sym(n):', 680, 345, { size: 21, weight: 600, align: 'left', alpha: a3 });
      c.text('its transitive normal subgroups are', 680, 385, { size: 20, align: 'left', alpha: a3 });
      c.text('Alt(n), Sym(n): no marks while it stays giant', 680, 415, { size: 20, align: 'left', weight: 600, alpha: a3 });
      const a4 = b.on(4);
      c.text('tight:', 110, 530, { size: 22, weight: 600, align: 'left', alpha: a4 });
      c.tex('\\mathrm{Alt}(\\kappa)^r\\text{ acting on itself from both sides}', 190, 530, { size: 24, align: 'left', alpha: a4 });
      c.tex('\\sigma\\ge r\\kappa,\\quad \\log n = r\\log(\\kappa!/2)', 190, 575, { size: 24, align: 'left', alpha: a4 });
      const a5 = b.on(5);
      c.text('at most O(log n) unaffected steps on any chain', 640, 640, { size: 25, weight: 600, alpha: a5 });
    },
  });
})();
