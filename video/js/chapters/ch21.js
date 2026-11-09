/* Chapter 21: degree d, a smaller class of groups. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.part('Part VI: bounded degree');
  V.chapter('degree', 'Degree d: a smaller class of groups');

  V.scene({
    beats: [
      'One more thing, and it is not in the paper. If the analysis below is right, the same machinery does better when the input has a bounded degree: when every vertex touches at most d others. This chapter and the next two are about that, and they have a different status from everything so far. I will spell the status out at the end. Please hold the two things apart.',
      'Luks\'s 1982 reduction is the starting point. Fix one edge. Now the graph has a root. Reveal the rest in layers, by distance from that edge.',
      'A vertex in one layer has at most d minus 1 children in the next. So when we extend an automorphism by one layer, what is left to choose is a permutation of the children of each vertex, which is a permutation of at most d minus 1 things.',
      'A chain of these choices, one layer at a time, is exactly a sequence of string-isomorphism problems, each under a group built by stacking symmetric groups on at most d minus 1 points. The reduction is polynomial time, and it does not depend on d.',
      'So the question becomes: how fast can string isomorphism be, if every group in sight is built from such small pieces?',
    ],
    draw(c_, b) {
      D.title('Luks\'s reduction: layers from a fixed edge', { alpha: b.on(0) });
      const a = b.on(1);
      // layered tree drawing
      const rootL = [560, 120], rootR = [720, 120];
      const layer1 = [430, 520, 610, 700, 790, 880];
      const y1 = 240, y2 = 400, y3 = 560;
      const a1 = b.on(1);
      c.line(rootL[0], rootL[1], rootR[0], rootR[1], { stroke: C.lab, lw: 5, alpha: a1 });
      c.circle(rootL[0], rootL[1], 14, { fill: C.lab, alpha: a1 }); c.circle(rootR[0], rootR[1], 14, { fill: C.lab, alpha: a1 });
      c.text('fixed edge', 640, 90, { size: 20, fill: C.ink2, alpha: a1 });
      const parent1 = [0, 0, 0, 1, 1, 1];
      layer1.forEach((x, i) => { const p = parent1[i] ? rootR : rootL; c.line(p[0], p[1], x, y1, { stroke: C.ink3, alpha: a1 }); c.circle(x, y1, 11, { fill: C.bg3, stroke: C.ink2, alpha: a1 }); });
      c.text('≤ d − 1 children', 975, 195, { size: 19, fill: C.ink2, align: 'left', alpha: a1 });
      // next layers, simplified
      const a2 = b.on(2);
      const y2xs = [];
      layer1.forEach((x, i) => { [-30, 30].forEach((dx) => { const nx = x + dx; y2xs.push(nx); c.line(x, y1, nx, y2, { stroke: C.ink3, alpha: a2 }); c.circle(nx, y2, 8, { fill: C.bg3, stroke: C.ink2, alpha: a2 }); }); });
      c.rect(385, 370, 180, 60, { stroke: C.violet, lw: 3, r: 9, alpha: a2 });
      c.tex('\\mathrm{Sym}(\\le d-1)', 975, 355, { size: 22, alpha: a2, align: 'left' });
      c.text('per parent: a small permutation', 980, 400, { size: 19, fill: C.ink2, align: 'left', alpha: a2 });
      const a3 = b.on(3);
      c.tex('\\text{iterated wreath products of } \\mathrm{Sym}(\\le d-1)', 640, 590, { size: 28, alpha: a3 });
      D.simplified(640, 640, a3, 'layer picture: actual reduction is a recursion over these layers');
      D.chip('not in the HJ paper', 150, 90, { alpha: b.on(0), stroke: C.orange, textFill: C.ink, size: 18 });
    },
  });

  V.scene({
    beats: [
      'The class of groups is called Gamma hat d, from Grohe, Neuen and Schweitzer: every composition factor embeds in the symmetric group on d points. A composition factor is one of the simple pieces, like Alt five.',
      'Two facts about this class. First, it is closed: subgroups and quotients of a group in the class are in the class. And the algorithm only ever builds subgroups, quotients, cosets inside its current group. So the algorithm never leaves the class.',
      'Second, and this is the whole point. A giant on q labels means an alternating group Alt q is a quotient of the group, so it is one of the composition factors. In this class, that factor embeds in Sym d, and for q at least 5 that forces q to be at most d.',
      'So every giant has q at most d. Think about what that does. If d is at most N to the alpha, then q is at most lambda, and the giant step never takes the wide branch.',
      'Look at the algorithm flow. The wide-giant branch, the row step, the row terminal, the columns, the in-domain rectangles: all of them only run for q greater than lambda. They simply do not occur. Every auxiliary configuration is the small kind, on q squared positions, a fresh call that stays in the class.',
      'That is the first big simplification. The second one is about the wallet.',
    ],
    draw(c_, b) {
      D.title('The class \\hat{Γ}_{d}, and what it removes', { alpha: b.on(0) });
      const a = b.on(0);
      c.tex('G\\in\\hat\\Gamma_d\\iff\\text{ every composition factor of } G \\text{ embeds in } \\mathrm{Sym}(d)', 640, 112, { size: 25, alpha: a });
      const a1 = b.on(1);
      c.text('closed under subgroups and quotients', 640, 165, { size: 22, alpha: a1 });
      const a2 = b.on(2);
      c.tex('\\mathrm{Alt}(q)\\text{ a section, }q\\ge5\\quad\\Rightarrow\\quad q\\le d', 640, 220, { size: 29, alpha: a2 });
      const a3 = b.on(3);
      c.tex('d\\le N^{\\alpha}=\\lambda\\quad\\Rightarrow\\quad q\\le\\lambda\\ \\text{ always}', 640, 278, { size: 26, alpha: a3 });
      // Flow chart with grey-outs
      const a4 = b.on(4);
      const boxes = [
        ['GiantStep', 180, 400, false], ['q ≤ λ', 340, 400, false], ['small configuration', 545, 400, false], ['q > λ', 180, 500, true], ['Row step', 340, 500, true], ['Row terminal', 545, 500, true], ['columns', 790, 500, true],
      ];
      const arrows = [[250, 400, 300, 400], [380, 400, 440, 400], [180, 430, 180, 468], [220, 500, 290, 500], [395, 500, 470, 500], [620, 500, 720, 500]];
      arrows.forEach((ar, i) => c.arrow(ar[0], ar[1], ar[2], ar[3], { stroke: C.ink3, alpha: a4 * (i >= 2 ? 0.28 : 0.9), lw: 2 }));
      boxes.forEach(([label, x, y, gone]) => D.box(x, y, 150, 56, label, { alpha: a4 * (gone ? 0.28 : 1), size: 17, stroke: gone ? C.rule : C.aqua }));
      if (a4 > 0) { c.line(120, 460, 900, 540, { stroke: C.red, lw: 3, alpha: a4 * 0.75 }); c.line(900, 460, 120, 540, { stroke: C.red, lw: 3, alpha: a4 * 0.75 }); c.text('never runs when d ≤ λ', 1040, 500, { size: 22, weight: 650, alpha: a4 }); }
      c.text('Everything else stays in the class \\hat{Γ}_{d}', 640, 620, { size: 25, alpha: b.on(4), weight: 600 });
    },
  });
})();
