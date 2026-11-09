/* Chapter 13: where the rectangle lives. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr;
  V.chapter('live', 'Where the rectangle lives');
  V.scene({
    beats: [
      'There is a catch in stopping at the first rectangle. Who solves it? We need the answer under exactly the relabelings that the current group allows. And a rectangle on q labels has up to q squared cells.',
      'If q is small, there is no problem. Write N for the number of positions when the current phase of the recursion began; chapter 15 explains phases. Let lambda be N to the alpha, with alpha two fifths. When q is at most lambda, solve the configuration fresh, on its q squared positions. That is at most N to the 2 alpha, which is well below the threshold of the phase.',
      'If q is bigger than lambda, q squared might be larger than the whole domain. So a fresh call on q squared positions is out of the question. The rectangle has to be solved somewhere inside the positions that we already have.',
      'Here is the good news. Above lambda, a lemma in the paper pins down the action: the orbits of the kernel on positions are indexed by single labels, by ordered pairs, or by unordered pairs of labels. Those are the only ways.',
      'If they are pairs: pull each matrix entry back to all positions over that pair. The positions over W times R form an orbit Delta of a subgroup. Its size is a fraction of s, at most theta: a constant smaller than 1. So the recursive call is on a genuinely smaller orbit, which keeps all of its inherited hierarchy, and caps, and budget.',
      'And that orbit call is what pays for the rectangle query: the domain decreases by a constant factor.',
    ],
    draw(c_, b) {
      D.title('Where does the rectangle live?', { alpha: b.on(0) });
      const a1 = b.on(1), a2 = b.on(2);
      // Case panels
      D.card(70, 110, 350, 245, { alpha: a1, stroke: C.aqua });
      c.tex('q\\le\\lambda=N^{\\alpha}', 245, 150, { size: 27, alpha: a1 });
      c.text('a fresh call on C×C', 245, 196, { size: 20, alpha: a1 });
      c.tex('\\le N^{2\\alpha}\\ \\text{positions}', 245, 236, { size: 24, alpha: a1 });
      c.text('solved on its own', 245, 285, { size: 19, fill: C.ink2, alpha: a1 });
      c.text('well below the phase threshold', 245, 312, { size: 19, fill: C.ink2, alpha: a1 });

      D.card(460, 110, 750, 245, { alpha: a2, stroke: C.orange });
      c.tex('q>\\lambda', 835, 150, { size: 27, alpha: a2 });
      c.tex('\\text{cannot afford } q^2\\ \\text{fresh positions}', 835, 195, { size: 24, alpha: a2 });
      const a3 = b.on(3);
      const opts = [['kernel orbit ↔ a label', C.lab], ['kernel orbit ↔ ordered pair', C.lab], ['kernel orbit ↔ unordered pair', C.lab]];
      opts.forEach(([t, col], i) => {
        c.rect(490 + i * 240, 240, 220, 80, { fill: C.bg3, r: 8, alpha: a3 });
        c.text(t, 600 + i * 240, 280, { size: 16, alpha: a3 });
      });
      // Pair pull-back picture
      const a4 = b.on(4);
      const gx = 120, gy = 400, cell = 18;
      for (let i = 0; i < 10; i++) for (let j = 0; j < 10; j++) {
        const inW = j >= 2 && j <= 9, inR = i >= 7 && i < 10;
        c.rect(gx + i * cell, gy + j * cell, cell - 2, cell - 2, { fill: inW && inR ? C.blue : C.bg3, r: 2, alpha: a4 });
      }
      c.text('W × R', gx + 8.5 * cell, gy - 16, { size: 18, alpha: a4 });
      c.text('labels Γ × labels Γ', gx + 5 * cell, gy + 10 * cell + 28, { size: 17, fill: C.ink2, alpha: a4 });
      c.arrow(420, 490, 540, 490, { stroke: C.ink2, alpha: a4, lw: 3 });
      c.text('pull entries back', 480, 465, { size: 17, fill: C.ink2, alpha: a4 });
      c.rect(560, 400, 320, 200, { stroke: C.ink2, lw: 2, r: 10, alpha: a4 });
      c.rect(600, 450, 240, 100, { fill: C.pos, r: 8, alpha: a4 * 0.75 });
      c.text('Δ', 720, 500, { size: 30, weight: 600, fill: '#111', alpha: a4 });
      c.text('existing positions Ω', 720, 425, { size: 18, fill: C.ink2, alpha: a4 });
      const a5 = b.on(5);
      c.tex('\\frac{|\\Delta|}{s}\\le\\frac{2|W||R|}{q(q-1)}\\le\\theta<1', 1040, 500, { size: 30, alpha: Math.max(a4, 0), fill: C.ink });
      c.text('hierarchy, caps, σ all inherited', 1040, 560, { size: 19, fill: C.ink2, alpha: a4 });
      c.text('domain decrease pays', 1040, 610, { size: 22, weight: 600, alpha: a5 });
    },
  });

  // Rows and columns
  V.scene({
    beats: [
      'The remaining case is the single-label one. Each position sits over one label, and the labels are permuted by the giant. Regard the fibres over the labels as rows. Then there are m rows, each a copy of the same set of within-row coordinates.',
      'The paper\'s row normal form lets us choose coordinates so that even permutations of the rows act independently of what happens inside a row. It also describes the leftover variation inside a row.',
      'If that variation is transitive inside a row, the rows are all the same object, and the row terminal solves the problem with polynomially many exact calls on single rows. Tying them together costs exp of log squared N, additive, once.',
      'If it is intransitive, its orbits are columns. And now the positions form a grid: rows by columns. Crucially, we keep the row action, even though we are about to work on the columns. A later rectangle on the column labels is solved by a diagonal coupling with the retained rows.',
      'Couple the even permutations on q column labels with the same permutations of q selected rows. That is a real subgroup orbit, and on it the rectangle shows up as a grid of equal cells, using at most a quarter of the positions.',
      'The diagonal subgroup is used only for this query. Its index in the parent is never enumerated. The parent goes on under the lifted matrix answer.',
      'And if a later column action has q larger than the number of rows m, we can enlarge the rows once. But only once: after that, the other factors of the hierarchy have product below lambda, so no third large degree can appear. A counter h, starting at two, tracks those row events.',
    ],
    draw(c_, b) {
      D.title('Rows, columns, and a diagonal', { alpha: b.on(0) });
      const a = b.on(0);
      const x0 = 110, y0 = 120, cols = 10, rows = 8, cw = 44, ch = 44;
      for (let i = 0; i < cols; i++) for (let j = 0; j < rows; j++) c.rect(x0 + i * cw, y0 + j * ch, cw - 4, ch - 4, { fill: C.pos, r: 3, alpha: a * 0.28 });
      c.text('m rows', x0 - 45, y0 + 4 * ch, { size: 19, fill: C.ink2, alpha: a });
      // Normal form: row permutation arrow
      const a1 = b.on(1);
      c.arrow(x0 + 5 * cw, y0 - 18, x0 + cw, y0 - 18, { stroke: C.lab, lw: 4, alpha: a1 });
      c.text('even permutations of the rows: independent', x0 + 5.5 * cw, y0 - 40, { size: 18, alpha: a1 });
      // Columns
      const a3 = b.on(3);
      for (let i = 0; i < cols; i += 3) c.rect(x0 + i * cw - 3, y0 - 3, 3 * cw + 2 - 4, rows * ch, { stroke: C.aqua, lw: 2.5, r: 6, alpha: a3 });
      c.text('columns: orbits of the variation', 760, 170, { size: 21, weight: 600, align: 'left', alpha: a3 });
      // Terminal
      const a2 = b.on(2, 3);
      D.card(760, 130, 420, 170, { alpha: a2 });
      c.text('Variation transitive in a row:', 780, 165, { size: 21, weight: 600, align: 'left', alpha: a2 });
      c.text('row terminal', 780, 200, { size: 20, align: 'left', alpha: a2 });
      c.tex('\\exp(O(\\log^2 N))\\ \\text{additive}', 780, 245, { size: 23, align: 'left', alpha: a2, fill: C.ink });
      c.text('polynomially many exact calls on one row', 780, 278, { size: 17, fill: C.ink2, align: 'left', alpha: a2 });
      // Diagonal coupling
      const a4 = b.on(4);
      for (let i = 0; i < 8; i++) c.rect(x0 + i * cw + 2, y0 + i * ch + 2, cw - 8, ch - 8, { fill: C.mag, r: 3, alpha: a4 * 0.8 });
      c.text('diagonal: columns coupled to q selected rows', 760, 245, { size: 20, weight: 600, align: 'left', alpha: a4 });
      c.tex('\\frac{|W||R|}{mq}\\le\\frac{q}{4m}\\le\\frac14', 960, 330, { size: 30, alpha: a4 });
      const a5 = b.on(5);
      c.text('used only for the query; its index is never enumerated', 950, 400, { size: 20, alpha: a5 });
      const a6 = b.on(6);
      c.rect(700, 470, 480, 170, { fill: C.bg2, stroke: C.h, lw: 2.5, r: 10, alpha: a6 });
      c.text('one enlargement, at most', 940, 508, { size: 24, weight: 600, alpha: a6 });
      c.tex('\\frac{N}{mq}<N^{1-2\\alpha}<\\lambda', 940, 555, { size: 26, alpha: a6 });
      c.tex('h\\in\\{0,1,2\\}', 940, 605, { size: 26, fill: C.h, alpha: a6 });
      D.simplified(330, 610, b.on(4), 'clean grid drawn; the paper handles general fibre structure');
    },
  });
})();
