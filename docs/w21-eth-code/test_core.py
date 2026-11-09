#!/usr/bin/env python3
"""Exact small-case tests of the preprint's Sec. 2-4 identities, with deliberately broken variants.
Usage: python3 test_core.py [--quick]"""
import sys, time, itertools, random
from fractions import Fraction as Fr
from math import comb, exp
from eth_core import *

BROKEN_MATRIX = ['f_wrong', 'no_V0']
BROKEN_DESIGN = ['C_drop', 'C_empty', 'phi_drop', 'sigma_split', 'measure_mod2']
BROKEN_RECOVER = ['no_restore', 'J_short', 'E_short']
DIAG = []

def test_remark44():
    C = Construction(2, 2, 2, A0=0)
    assert C.I == [0, 1]
    u = ((0, 1), (0, 1))  # (a,d)=(00,11)
    row = C.P_u(u)
    z0, z1, z2, z12 = u, ((1, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 0), (1, 0))
    assert row[z0] == [Fr(1)]
    assert row[z1] == [Fr(0), Fr(-1, 2)]
    assert row[z2] == [Fr(0), Fr(-1)]
    assert z12 not in row or row[z12] == [Fr(0)]
    return True

def matrix_checks(C, sample_psi=None, seed=0):
    r, Q, R = C.r, C.Q, C.R
    us = list(C.all_u())
    D = len(us)
    assert D == C.D
    rng = random.Random(seed)
    psis = list(itertools.product(C.choices, repeat=Q))
    if sample_psi and len(psis) > sample_psi:
        psis = rng.sample(psis, sample_psi)
    res = {'eig_ok': True, 'support_ok': True, 'rank_ok': True}
    mrows = {u: C.M0_row(u) for u in us}
    # support (Lemma 4.2)
    for u in us:
        for y in mrows[u]:
            if len(C.E(u, y)) > R - 1:
                res['support_ok'] = False
    # eigen-relation (Lemma 4.1 proof)
    for ch in psis:
        j = C.jval(ch)
        lam = Fr((-1) ** j) * C.f_value(j)
        if 'no_V0' in C.broken:
            lam = C.f_value(j)
        if j in C.I and lam != 1:
            res['eig_ok'] = False
        for u in us:
            lhs = sum((c * C.psi(ch, y) for y, c in mrows[u].items()), Fr(0))
            if lhs != lam * C.psi(ch, u):
                res['eig_ok'] = False
                break
    # rank(I - M0) <= c^B, exact, D small
    c = len(C.exceptional)
    res['c'] = c
    if D <= 81:
        idx = {u: i for i, u in enumerate(us)}
        rows = []
        for u in us:
            v = [Fr(0)] * D
            v[idx[u]] = Fr(1)
            for y, cc in mrows[u].items():
                v[idx[y]] -= cc
            rows.append(v)
        rk = rank_exact(rows, D)
        res['rank'] = rk
        res['rank_ok'] = rk <= c
    res['frac_exceptional'] = Fr(c, D)
    res['hoeffding'] = 2 * exp(-R * R / (8 * Q))
    return res


def lemma43_check(C, max_u=None, seed=0):
    """Array-level Lemma 4.3: for u, t, g != d_u(t), P_u(t)|S^B_{t,g} lies in the row space of
    C^B restricted to S^B_{t,g}. Exact rational. Returns (checked, failed)."""
    rng = random.Random(seed)
    us = list(C.all_u())
    if max_u and len(us) > max_u:
        us = rng.sample(us, max_u)
    rows_all = [{u: C.psi(ch, u) for u in C.all_u() if C.psi(ch, u)} for ch in C.exceptional]
    checked = failed = 0
    for u in us:
        row = C.P_u(u)
        for t in range(1, C.Q + 1):
            du = u[t - 1][1]
            for g in range(C.r):
                if g == du:
                    continue
                columns = [y for y in C.all_u() if y[t - 1][0] == g]
                colset = set(columns)
                target = {y: peval(p, t) for y, p in row.items() if y in colset and peval(p, t) != 0}
                rr = [{y: x for y, x in rw.items() if y in colset} for rw in rows_all]
                rr = [z for z in rr if z]
                checked += 1
                if not in_rowspace(rr, target, columns):
                    failed += 1
    return checked, failed

def pipeline(cfg, n, m, seed, broken=(), width=3, occ=3, want_min_qE=False):
    r, Q, R = cfg
    clauses = random_cnf(n, m, seed, width=width, occ=occ)
    count = count_cnf(n, clauses)
    C = Construction(r, Q, R, broken=broken)
    d = build_cnf_design(C, n, clauses, seed + 1000, broken=broken)
    M = d.M
    dT = M * (R - 1)              # deg_T H <= M(R-1) because deg P <= R-1 (paper uses MR)
    q = dT // Q
    J = q + 1
    ring_T = Ring(dT + 2)
    H = ring_T.to_list(d.H_poly(ring_T))
    deg_actual = max((i for i, c in enumerate(H) if c != 0), default=0)
    tdep = sum(1 for row in d.P.values() if any(len(p) > 1 for p in row.values()))
    report = dict(n=n, M=M, h=d.h, q=q, J=J, D=C.D, count=count, deg_actual=deg_actual, tdep=tdep, qE_used=q)
    report['H0'] = H[0]
    report['H0_ok'] = H[0] == count
    report['deg_ok'] = all(c == 0 for c in H[dT + 1:])
    design_bad = 0; design_checked = 0
    for t in range(1, Q + 1):
        ck, f = d.check_design(t)
        design_checked += ck; design_bad += f
    report['design'] = (design_checked, design_bad)
    # separation at each t: compare factorized H(t) with brute H(t)
    sep_ok = True
    for t in range(1, Q + 1):
        ring0 = Ring(1)
        val = ring0.to_list(d.Z_factorized(t, set(), set(), ring0))[0]
        if val != peval(H, t):
            sep_ok = False
    report['sep_ok'] = sep_ok
    # Taylor data by inclusion-exclusion and comparison with brute shift
    tay_ok = True
    data = {}
    if 'E_short' in broken:
        # one below the X-degree the truncation must cover at this instance
        qE = max(min(q, deg_actual) - 1, 0)
    else:
        qE = q
    report['qE_used'] = qE
    for t in range(1, Q + 1):
        ring = Ring(J)
        got = ring.to_list(d.taylor_IE(t, qE, ring))
        exp_ = pshift(H, t, J)
        if got != exp_:
            tay_ok = False
        for j in range(J):
            data[(t, j)] = got[j]
    report['taylor_ok'] = tay_ok
    Jrec = J
    if 'J_short' in broken:
        Jrec = deg_actual // Q          # then Q*Jrec <= deg H: under-determined on purpose
        report['Jrec'] = Jrec
    if Jrec >= 1:
        coeffs = hermite_solve(Q, Jrec, data)
        report['recovered'] = coeffs[0]
        report['recover_ok'] = coeffs[0] == count
    else:
        report['recovered'] = None
        report['recover_ok'] = True   # J'=0 not applicable (deg H < Q): cannot be broken this way
    report['applicable'] = Jrec >= 1
    if want_min_qE:
        report['min_qE'] = None
        for qq in range(0, q + 1):
            allgood = True
            for t in range(1, Q + 1):
                ring = Ring(J)
                if ring.to_list(d.taylor_IE(t, qq, ring)) != pshift(H, t, J):
                    allgood = False
                    break
            if allgood:
                report['min_qE'] = qq
                break
    return report

INSTANCES = {
    'sparse-A': ((2, 3, 2), 6, 5, 3),
    'sparse-B': ((2, 4, 2), 6, 4, 3),
    'sparse-C': ((3, 2, 2), 6, 4, 3),
    'sparse-D': ((2, 4, 3), 5, 4, 3),
    'dense-A': ((2, 3, 2), 5, 8, 6),
    'dense-B': ((3, 2, 2), 5, 6, 6),
    'dense-C': ((2, 4, 2), 7, 6, 5),
}

def run_correct(names, seeds, want_min=False):
    allok = True
    for name in names:
        cfg, n, m, occ = INSTANCES[name]
        for s in seeds:
            t1 = time.time()
            rep = pipeline(cfg, n, m, s, occ=occ, want_min_qE=want_min)
            ok = rep['H0_ok'] and rep['deg_ok'] and rep['sep_ok'] and rep['taylor_ok'] and rep['recover_ok'] and rep['design'][1] == 0
            allok &= ok
            mn = f" min_qE={rep['min_qE']}" if want_min else ''
            print(f"  {name} {cfg} seed={s} n={n} M={rep['M']} h={rep['h']} q={rep['q']} degH={rep['deg_actual']}/{rep['M']*(cfg[2]-1)} Tdep_rows={rep['tdep']}/{rep['M']} "
                  f"#F={rep['count']} H0={rep['H0_ok']} deg={rep['deg_ok']} design={rep['design']} sep={rep['sep_ok']} taylor={rep['taylor_ok']} hermite={rep['recover_ok']}{mn} ({time.time()-t1:.1f}s)", flush=True)
    return allok

BROKEN_ALL = ['C_drop', 'C_empty', 'phi_drop', 'sigma_split', 'measure_mod2', 'f_wrong', 'no_V0', 'no_restore', 'J_short', 'E_short']

def run_broken(pairs, variants):
    # pairs: list of (instance name, seed)
    for b in variants:
        caught = 0; total = 0; na = 0; detail = []
        for name, s in pairs:
            cfg, n, m, occ = INSTANCES[name]
            for _ in [0]:
                total += 1
                rep = pipeline(cfg, n, m, s, occ=occ, broken=[b])
                flags = []
                if rep['design'][1] > 0: flags.append('design')
                if not rep['sep_ok']: flags.append('sep')
                if not rep['taylor_ok']: flags.append('taylor')
                if not rep['recover_ok']: flags.append('recover')
                if not rep['H0_ok']: flags.append('H0')
                if not rep.get('applicable', True):
                    na += 1
                    flags.append('n/a')
                elif flags:
                    caught += 1
                detail.append('+'.join(flags) or 'none')
        print(f'  {b:14s} caught {caught}/{total-na} (n/a {na})  [{"; ".join(detail)}]', flush=True)

def main():
    args = set(sys.argv[1:])
    t0 = time.time()
    if 'matrix' in args or not args:
        print('Remark 4.4 worked example matches:', test_remark44())
        print('\n== Matrix checks (exact) ==')
        cfgs = [(2, 2, 2), (2, 3, 2), (3, 2, 2), (2, 4, 2), (2, 4, 3)]
        for cfg in cfgs:
            C = Construction(*cfg)
            res = matrix_checks(C, sample_psi=None if C.D <= 81 else 60)
            print(f'  (r,Q,R)={cfg} D={C.D} I={C.I} c^B={res["c"]} '
                  f'c/D={float(res["frac_exceptional"]):.3f} hoeff={res["hoeffding"]:.3f} '
                  f'eig={res["eig_ok"]} support={res["support_ok"]} rank={res.get("rank","-")} rank<=c:{res["rank_ok"]}', flush=True)
            assert res['eig_ok'] and res['support_ok'] and res['rank_ok']
        for b in BROKEN_MATRIX:
            for cfg in [(2, 3, 2), (2, 4, 3)]:
                C = Construction(*cfg, broken=[b])
                res = matrix_checks(C, sample_psi=60)
                print(f'  BROKEN {b} {cfg}: eig={res["eig_ok"]} support={res["support_ok"]}', flush=True)
        print('\n== Lemma 4.3 at array level (exact row-space membership) ==')
        for cfg in [(2, 2, 2), (2, 3, 2), (3, 2, 2)]:
            for b in [None, 'C_drop', 'C_empty', 'phi_drop', 'f_wrong', 'no_V0']:
                if cfg == (2, 2, 2) and b == 'C_drop':
                    pass
                C = Construction(*cfg, broken=[b] if b else ())
                ck, fl = lemma43_check(C, max_u=64)
                print(f'  {cfg} variant={b or "correct"}: checked {ck} failed {fl}', flush=True)
    if 'correct' in args or not args:
        print('\n== Correct construction, sparse instances ==')
        run_correct(['sparse-A', 'sparse-B', 'sparse-C', 'sparse-D'], range(3))
        print('\n== Correct construction, dense instances (arrays well filled) ==')
        ok = run_correct(['dense-A', 'dense-B'], range(3))
        print('  ALL PASS:', ok)
    if 'denseC' in args:
        print('\n== Correct, dense-C (q < n; reports minimal |E| truncation) ==')
        run_correct(['dense-C'], range(2), want_min=True)
    if 'broken' in args or not args:
        print('\n== Broken variants, instances with many T-dependent rows ==')
        run_broken([('dense-A', 1), ('dense-A', 2), ('dense-B', 1), ('dense-B', 2), ('sparse-D', 0), ('sparse-D', 2)], BROKEN_ALL)
    if 'brokenC' in args:
        print('\n== Broken variants needing q<n: dense-C ==')
        run_broken([('dense-C', 0), ('dense-C', 1)], ['E_short', 'J_short'])
    print('\nTotal time %.1fs' % (time.time() - t0))

if __name__ == '__main__':
    main()
