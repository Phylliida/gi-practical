/* Chapter 24: what is proved, what is not; the code. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr; const DATA = window.DATA;
  V.part('Coda');
  V.chapter('status', 'What is proved, and what is not');
  const K = DATA.constants;
  V.scene({
    beats: [
      'A last honest summary of the main result, the n to the order log n bound.',
      'It is a preprint, from November 2026, and it has not been refereed. Its main theorem has been formalized in Lean. That formalization writes the whole algorithm as one program for a simple machine and proves correctness and the time bound, and it is accepted by the comparator tool.',
      'It assumes ten results from the literature as axioms. Six are structural facts about groups, four are about permutation-group algorithms. All ten depend on the classification of finite simple groups.',
      'The constant in the exponent is not explicit. Just from what the paper needs, kappa at least 64 forces a certain cutoff of at least 258, a constant a of at least about 2450, and A of at least about 19 thousand. And that multiplies a constant C of at least 128 from the sigma bound, whose full value isn\'t even written down.',
      'So the bound is enormous. The real content here is structural: a precise account of what forces graph isomorphism to cost what it costs, and a pair of ideas that took one logarithm away.',
    ],
    draw(c_, b) {
      D.title('What is proved', { alpha: b.on(0) });
      const a1 = b.on(1), a2 = b.on(2), a3 = b.on(3);
      D.card(90, 110, 500, 210, { alpha: a1 });
      c.text('arXiv:2611.01399, Nov 2026', 340, 145, { size: 23, weight: 600, alpha: a1 });
      c.text('not refereed', 340, 180, { size: 21, fill: C.ink2, alpha: a1 });
      c.text('Lean: whole algorithm, one program,', 340, 230, { size: 21, alpha: a1 });
      c.text('correctness and time bound', 340, 258, { size: 21, alpha: a1 });
      c.text('accepted by comparator', 340, 290, { size: 19, fill: C.ink2, alpha: a1 });
      D.card(690, 110, 500, 210, { alpha: a2 });
      c.text('10 cited axioms', 940, 145, { size: 23, weight: 600, alpha: a2 });
      c.text('6 structural, 4 algorithmic', 940, 188, { size: 21, alpha: a2 });
      c.text('all rely on the classification', 940, 230, { size: 21, alpha: a2 });
      c.text('of finite simple groups', 940, 258, { size: 21, alpha: a2 });
      // constants
      D.card(90, 350, 1100, 215, { alpha: a3, stroke: C.red });
      c.text('Constants (lower bounds implied by the paper\'s own conditions)', 640, 385, { size: 22, weight: 600, alpha: a3 });
      c.text('κ ≥ 64', 170, 445, { size: 24, align: 'left', alpha: a3, weight: 600 });
      c.text('q₀ ≥ 258', 335, 445, { size: 24, align: 'left', alpha: a3, weight: 600 });
      c.text('a ≥ ' + Math.round(K.a_min), 510, 445, { size: 24, align: 'left', alpha: a3, weight: 600 });
      c.text('A ≥ ' + Math.round(K.A_enum).toLocaleString('en-US'), 700, 445, { size: 24, align: 'left', alpha: a3, weight: 600 });
      c.text('C ≥ 128', 960, 445, { size: 24, align: 'left', alpha: a3, weight: 600 });
      c.tex('\\text{root exponent}\\approx A\\cdot C\\cdot\\log^2 N\\ \\ \\ge\\ ' + Math.round(K.A_times_C / 1e5) / 10 + '\\times 10^{6}\\,\\log^2 N', 640, 510, { size: 28, alpha: a3 });
      c.text('the constant in C itself is not explicit', 640, 548, { size: 18, fill: C.ink2, alpha: a3 });
      c.text('The value is the structure, not the number.', 640, 625, { size: 28, weight: 650, alpha: b.on(4) });
    },
  });

  V.scene({
    beats: [
      'The final note is about this project itself, kept separate from everything above. The repository has a simplified Python solver that follows the shape of the algorithm, keeps every answer exact, and measures what happens. It is not the paper\'s algorithm: for example, its test sets have size 3, and it lacks the full machinery.',
      'What it found, in passing: a simplified version of this machinery runs, and stays exact, in pure Python. And on some hard families, like Neuen and Schweitzer\'s multipedes, a canonicalization variant is faster than nauty and Traces. On random regular graphs and on many others, nauty and Traces are far ahead. Benchmarks and their caveats are in the repository, with every answer checked.',
      'That is the end. Two logarithms left, and we can say what each of them pays for. And a third one, gone: not because the same step became cheaper, but because the algorithm stopped having to name a logarithmic number of labels at once. Thank you for watching.',
    ],
    draw(c_, b) {
      D.title('A separate note: the code in this repo', { alpha: b.on(0) });
      const a = b.on(0);
      D.card(120, 120, 1040, 170, { alpha: a });
      c.text('gi-practical: simplified, exact Python', 640, 160, { size: 25, weight: 600, alpha: a });
      c.text('test sets of size 3, not 64; not the paper\'s full algorithm', 640, 205, { size: 21, fill: C.ink2, alpha: a });
      c.text('every answer verified; benchmark notes and caveats live in the repo', 640, 245, { size: 21, fill: C.ink2, alpha: a });
      const a1 = b.on(1);
      c.text('A canonicalization variant is faster than nauty/Traces on multipedes,', 640, 340, { size: 22, alpha: a1 });
      c.text('and far slower on random regular graphs and many others.', 640, 372, { size: 22, alpha: a1 });
      D.simplified(640, 410, a1, 'not the algorithm of the video: a simplified Python relative');
      const a2 = b.on(2);
      D.bill(640, 520, [{ color: C.blue, alpha: a2 }, { color: C.lab, tex: 'O(1)', alpha: a2 }, { color: C.aqua, alpha: a2 }], { w: 120, h: 58, size: 26 });
      c.text('The Third Logarithm', 640, 628, { size: 34, weight: 700, alpha: a2 });
    },
  });
})();
