/* Chapter 5: orbits, blocks, primitive. */
(function () {
  const { C, c, lerp } = V; const D = window.Dr; const DATA = window.DATA;
  V.chapter('blocks', 'Orbits, blocks, primitive');
  const hex = DATA.hexagon;
  const hexPos = (cx, cy, R) => D.circle(6, cx, cy, R, -Math.PI / 2);
  const rot = [1, 2, 3, 4, 5, 0], refl = [0, 5, 4, 3, 2, 1];
  const compose = (a, b) => a.map((x) => b[x]);

  V.scene({
    beats: [
      'Back to a simple shape. A hexagon has six positions and twelve symmetries, six rotations and six reflections. Those twelve are our group G.',
      'Applying a symmetry moves positions around. The set of places a position can reach is its orbit. Here every position can reach every other, so there is just one orbit. We say G is transitive.',
      'Shrink the group. Keep only the symmetries that fix position 0. Two survive: doing nothing, and one reflection. Now the orbits are smaller: 0 alone, 3 alone, the pair 1 and 5, the pair 2 and 4.',
      'Orbits are the pieces a group cannot mix. When a group has several orbits, we can deal with them one at a time.',
      'Back on the 10-vertex graph, here is the table from before, coloured by orbit under its 120 symmetries: 10 diagonal positions, 30 ordered edges, 60 ordered non-edges. Those are computed numbers. Three orbits is all the structure the table has under this group.',
    ],
    draw(c_, b) {
      D.title('Orbits', { alpha: b.on(0) });
      const P = hexPos(330, 370, 170);
      // animate through some symmetries during beat 0/1
      let g = [0, 1, 2, 3, 4, 5];
      let next = g, f = 0;
      if (b.in(0, 2)) {
        const seq = [rot, rot, refl, rot, refl, rot, rot];
        const tt = (b.t - b.s(0)) * 0.65;
        const k = Math.floor(tt) % seq.length;
        f = D.ease(Math.min(1, (tt - Math.floor(tt)) * 2));
        for (let i = 0; i < k; i++) g = compose(g, seq[i]);
        next = compose(g, seq[k]);
      }
      const posNow = P.map((_, i) => [lerp(P[g[i]][0], P[next[i]][0], f), lerp(P[g[i]][1], P[next[i]][1], f)]);
      const orbCol = (i) => {
        if (b.t < b.s(2) - 0.2) return C.blue;
        return [C.blue, C.aqua, C.orange, C.yellow, C.orange, C.aqua][i];
      };
      D.graph(b.in(2) ? P : posNow, [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]], { r: 22, fill: orbCol, alpha: b.on(0), labels: (i) => i, labelSize: 22, labelFill: '#111' });
      if (b.in(1, 2)) c.text('one orbit', 330, 620, { size: 26, weight: 600, alpha: b.on(1, 2) });
      if (b.in(2)) {
        const a = b.on(2);
        c.text('stabilizer of 0: orbits {0}, {3}, {1,5}, {2,4}', 330, 620, { size: 22, alpha: a });
        c.circle(P[0][0], P[0][1], 31, { stroke: C.ink, lw: 2.5, alpha: a });
      }
      // right: the orbit-coloured table (real orbit sizes)
      const a = b.on(4);
      if (a > 0) {
        const A = DATA.petersen.A; const cell = 30, x0 = 710, y0 = 130;
        for (let i = 0; i < 10; i++) for (let j = 0; j < 10; j++) {
          const col = i === j ? C.ink2 : A[i][j] ? C.blue : C.orange;
          c.rect(x0 + j * cell, y0 + i * cell, cell - 2.5, cell - 2.5, { fill: col, r: 2, alpha: a * (i === j ? 1 : A[i][j] ? 1 : 0.75) });
        }
        c.rect(x0, y0 + 320, 22, 22, { fill: C.ink2, r: 3, alpha: a }); c.text('10 diagonal', x0 + 32, y0 + 331, { size: 20, align: 'left', alpha: a });
        c.rect(x0 + 160, y0 + 320, 22, 22, { fill: C.blue, r: 3, alpha: a }); c.text('30 ordered edges', x0 + 192, y0 + 331, { size: 20, align: 'left', alpha: a });
        c.rect(x0, y0 + 356, 22, 22, { fill: C.orange, r: 3, alpha: a * 0.75 }); c.text('60 ordered non-edges', x0 + 32, y0 + 367, { size: 20, align: 'left', alpha: a });
      }
    },
  });

  // Block systems. partition: array assigning each vertex a class.
  const antipodal = [0, 1, 2, 0, 1, 2];
  const triangles = [0, 1, 0, 1, 0, 1];
  const adjacent = [0, 0, 1, 1, 2, 2];
  V.scene({
    beats: [
      'Now a subtler idea. Colour opposite positions alike. That partitions the hexagon into three pairs.',
      'Watch a symmetry act. Rotate by one step, and every pair lands exactly on another pair. The colour classes get permuted, but never torn apart. A partition with that property is called a block system.',
      'Compare the partition into neighbouring pairs. Rotate by one step, and pairs get torn apart: position 1 is paired with 0 before, but with 2 after. Not a block system.',
      'The hexagon has one more block system: two triangles, the even positions and the odd ones.',
      'A block system is a compression. Collapse each pair of opposite positions to a single point. Our group now acts on three points. Twelve symmetries become six: all of Sym(3). This action on blocks is called the quotient.',
      'Two symmetries vanish: doing nothing, and rotating 180 degrees. They fix every block. They form the kernel.',
      'So the problem stacks: a size 3 problem on the blocks, and for each block, a size 2 problem inside. Six is three times two. Remember those ratios, d one, d two, whose product is the number of positions. That stack is the idea the whole video runs on.',
    ],
    draw(c_, b) {
      D.title('Block systems', { alpha: b.on(0) });
      const cx1 = 330, cy = 340;
      const P = hexPos(cx1, cy, 160);
      const pal = [C.blue, C.orange, C.aqua];
      const drawHex = (part, Pcur, alpha) => {
        const edges = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]];
        D.graph(Pcur, edges, { r: 22, fill: (i) => pal[part[i]], alpha, labels: (i) => i, labelSize: 22, labelFill: '#111' });
      };
      // Scene states
      if (b.in(0, 3)) {
        const part = b.in(2) ? adjacent : antipodal;
        const uR = b.in(1, 3) ? b.p(b.in(2) ? 2 : 1, 0.2, 0.75) : 0;
        const rotPos = P.map((_, i) => P[(i + 1) % 6]);
        const Pcur = P.map((p, i) => [lerp(p[0], rotPos[i][0], uR), lerp(p[1], rotPos[i][1], uR)]);
        drawHex(part, Pcur, b.on(0, 3));
        const al = b.on(0, 3);
        if (b.in(1, 2)) { const a2 = b.on(1, 2); c.text('rotate by one step', cx1, 560, { size: 24, alpha: a2 }); c.text('pairs land on pairs: a block system', cx1, 596, { size: 22, fill: C.ink2, alpha: a2 * b.p(1, 0.7, 0.95) }); }
        if (b.in(2, 3)) { const a2 = b.on(2, 3); c.text('rotate by one step', cx1, 560, { size: 24, alpha: a2 }); c.text('pairs are torn apart: not a block system', cx1, 596, { size: 22, fill: C.ink2, alpha: a2 * b.p(2, 0.7, 0.95) }); }
      }
      if (b.in(3, 4)) { drawHex(triangles, P, b.on(3, 4)); c.text('two triangles', cx1, 576, { size: 24, alpha: b.on(3, 4) }); }
      // Quotient picture
      if (b.in(4)) {
        const a = b.on(4);
        drawHex(antipodal, P, a * 0.4);
        const Q = D.circle(3, 900, 372, 130, -Math.PI / 2);
        const u = b.p(4, 0, 0.35);
        c.line(Q[0][0], Q[0][1], Q[1][0], Q[1][1], { stroke: C.ink3, alpha: a }); c.line(Q[1][0], Q[1][1], Q[2][0], Q[2][1], { stroke: C.ink3, alpha: a }); c.line(Q[2][0], Q[2][1], Q[0][0], Q[0][1], { stroke: C.ink3, alpha: a });
        Q.forEach((p, i) => {
          const src = [(P[i][0] + P[(i + 3) % 6][0]) / 2, (P[i][1] + P[(i + 3) % 6][1]) / 2];
          const x = lerp(src[0], p[0], u), y = lerp(src[1], p[1], u);
          c.circle(x, y, 26, { fill: pal[i], alpha: a }); c.text(['A', 'B', 'C'][i], x, y + 0.5, { size: 22, weight: 700, fill: '#111', alpha: a });
        });
        c.text('quotient on 3 blocks: Sym(3), order ' + hex.quotient_order_on_pairs, 900, 548, { size: 22, alpha: a });
        const a2 = b.on(5);
        c.tex('\\text{kernel } = \\{\\mathrm{id},\\ \\text{rot}_{180}\\}', 900, 150, { size: 26, alpha: a2 });
        c.text('order ' + hex.kernel_pairs_size + ': fixes every block', 900, 184, { size: 21, fill: C.ink2, alpha: a2 });
        const a3 = b.on(6);
        c.tex('s = 6 = d_1 d_2 = 3\\cdot 2', 900, 610, { size: 30, alpha: a3 });
      }
    },
  });

  // Primitive + interactive block explorer.
  const pPet = D.petersenPos(900, 360, 200), pHex = hexPos(310, 360, 170);
  function minBlock(n, gens, a, b) {
    const parent = Array.from({ length: n }, (_, i) => i);
    const find = (x) => { while (parent[x] !== x) { parent[x] = parent[parent[x]]; x = parent[x]; } return x; };
    const union = (x, y) => { x = find(x); y = find(y); if (x === y) return false; parent[Math.max(x, y)] = Math.min(x, y); return true; };
    union(a, b); const q = [[a, b]];
    for (let i = 0; i < q.length; i++) for (const g of gens) {
      const [u, v] = [g[q[i][0]], g[q[i][1]]];
      const ru = find(u), rv = find(v);
      if (ru !== rv) { union(u, v); q.push([u, v]); }
    }
    const out = Array.from({ length: n }, (_, i) => find(i));
    return out;
  }
  const HEXG = hex.gens, PETG = DATA.petersen.aut_gens;
  V.scene({
    init: () => ({ picks: [[null, null], [null, null]], blocks: [null, null], touched: false }),
    onClick(x, y, ix) {
      const test = (pts, gi, n, gens) => {
        for (let v = 0; v < n; v++) {
          if (Math.hypot(pts[v][0] - x, pts[v][1] - y) < 26) {
            let p = ix.picks[gi];
            if (p[0] === null || (p[0] !== null && p[1] !== null)) { p = [v, null]; ix.blocks[gi] = null; }
            else if (p[0] !== v) { p = [p[0], v]; ix.blocks[gi] = minBlock(n, gens, p[0], p[1]); }
            ix.picks[gi] = p; ix.touched = true; return true;
          }
        }
        return false;
      };
      if (test(pHex, 0, 6, HEXG) || test(pPet, 1, 10, PETG)) return true;
      return false;
    },
    beats: [
      'Some groups have no block systems except the two boring ones: everything in one block, or every point in its own. Those groups are called primitive.',
      { say: 'Try it. Click two vertices of the hexagon. This computes the smallest block containing both, using only the group\'s generators. Some pairs give a genuine block. Others swell to the whole set.', hold: 3 },
      { say: 'Now try the same on the 10-vertex graph, under all 120 of its symmetries. Every pair you pick swells to everything. It is primitive.', hold: 3 },
      'Primitive groups are the atoms here. Block systems let you peel a transitive group apart, level by level, until each level is a primitive action. The recursion lives on those levels.',
    ],
    draw(c_, b, ix) {
      D.title('Primitive groups have no proper blocks', { alpha: b.on(0) });
      const a0 = b.on(0);
      const pal = [C.blue, C.orange, C.aqua, C.yellow, C.mag, C.green, C.violet, C.red, C.ink2, C.ink3];
      const col = (block, i) => (block ? pal[block[i] % pal.length] : C.bg3);
      const edges6 = [[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 0]];
      D.graph(pHex, edges6, { r: 22, fill: (i) => col(ix.blocks[0], i), alpha: a0, labels: (i) => i, labelSize: 21, labelFill: C.dark ? (ix.blocks[0] ? '#111' : C.ink) : (ix.blocks[0] ? '#111' : C.ink) });
      D.graph(pPet, DATA.petersen.edges, { r: 16, fill: (i) => col(ix.blocks[1], i), alpha: a0, labels: (i) => i, labelSize: 15, labelFill: ix.blocks[1] ? '#111' : C.ink });
      const ring = (pts, picks) => picks.forEach((p) => { if (p !== null) c.circle(pts[p][0], pts[p][1], 30, { stroke: C.ink, lw: 3, alpha: a0 }); });
      ring(pHex, ix.picks[0]); ring(pPet, ix.picks[1]);
      if (b.in(1) && b.t < b.e(2)) {
        D.tryIt(640, 650, 1, 'Try it: click two vertices on either figure');
      }
      c.text('hexagon: 12 symmetries', 310, 590, { size: 21, fill: C.ink2, alpha: a0 });
      c.text('10-vertex graph: 120 symmetries', 900, 620, { size: 21, fill: C.ink2, alpha: a0 });
      const describe = (blocks) => {
        if (!blocks) return null;
        const n = new Set(blocks).size;
        return n === 1 ? 'the whole set: no proper block' : (n + ' blocks of size ' + (blocks.length / n));
      };
      const d0 = describe(ix.blocks[0]), d1 = describe(ix.blocks[1]);
      if (d0) c.text(d0, 310, 630, { size: 22, weight: 600, alpha: a0 });
      if (d1) c.text(d1, 900, 655, { size: 22, weight: 600, alpha: a0 });
    },
  });
})();
