"""E1: Theorem G (pinning base row block) vs nauty on height-2 instances."""
import itertools, random, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ht2lib import *

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)
tot = ok = 0
t0 = time.time()

def gen(b, m, mode):
    Vs = list(itertools.product(range(b), repeat=m))
    x = {}
    gauge = {vp: rng.sample(range(b), b) for vp in Vs}
    base = tuple(0 for _ in range(m))
    for z in points(b, m):
        a, c, ap, cp = z[:m], z[m], z[m + 1:2 * m + 1], z[2 * m + 1]
        if a == base:  # pinning block: permutation-matrix style
            x[z] = 2 + int(gauge[ap][cp] == c)
        else:
            if mode == 'random':
                x[z] = rng.randrange(2)
            elif mode == 'matched':  # block = random permutation matrix
                x[z] = 0  # filled below with a random permutation matrix per block
            elif mode == 'struct':
                x[z] = (sum(a) + sum(ap) + c * cp) % 2
    if mode == 'matched':
        for a in Vs:
            if a == base:
                continue
            for ap in Vs:
                p = rng.sample(range(b), b)
                for c in range(b):
                    for cp in range(b):
                        x[(*a, c, *ap, cp)] = int(p[c] == cp)
    return x


WHICH = eval(sys.argv[2]) if len(sys.argv) > 2 else [(2, 1, 3), (3, 1, 3), (4, 1, 3), (2, 2, 3)]
for b, m, modes in WHICH:
    pred = ht2_pred(m)
    for trial in range(3):
        for mode in ['random', 'matched', 'struct']:
            x = gen(b, m, mode)
            g = random_gwp_element(b, 2 * m + 2, pred, rng)
            y = apply_g(x, g)
            noniso = rng.random() < 0.4
            if noniso:
                # flip a pair of entries in y far from the base structure
                pts = [z for z in y]
                for _ in range(200):
                    z1, z2 = rng.choice(pts), rng.choice(pts)
                    if y[z1] != y[z2]:
                        y[z1], y[z2] = y[z2], y[z1]
                        break
            cols = sorted(set(x.values()) | set(y.values()))
            cx, ox, sx = nauty_cert_and_order(b, pred, x, cols)
            cy, oy, sy = nauty_cert_and_order(b, pred, y, cols)
            naut_iso = (sx == sy and cx == cy)
            res, aut = theorem_G(b, m, x, y)
            tot += 1
            if res == 'NO_PIN':
                print('NO_PIN', b, m, mode); continue
            good = (res == naut_iso)
            res2, aut2 = theorem_G(b, m, x, x)
            good2 = (aut2 == ox)
            ok += int(good and good2)
            print(f"b={b} m={m} {mode:8s} N={b**(2*m+2)} nautyIso={naut_iso} thmG={res} aut_nauty={ox} aut_thmG={aut2} {'OK' if good and good2 else 'BAD'}")
print(f"{ok}/{tot} ok, {time.time()-t0:.1f}s")
