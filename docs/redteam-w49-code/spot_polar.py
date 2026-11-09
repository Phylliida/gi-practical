#!/usr/bin/env python3
"""Memo section 7, polar row: type of Q(v)=h(v,v) on F_4^k and arc-transitivity data, by exact count."""
def norm(x):  # F_4 = {0,1,2=w,3=w^2}; norm x^3
    return 0 if x == 0 else 1
def count(k):
    # singular nonzero vectors of Q(v)=sum N(v_i) over F_2
    s = 0
    for v in range(1, 4**k):
        q = 0; t = v
        for _ in range(k):
            q ^= norm(t & 3); t >>= 2
        if q == 0: s += 1
    return s
for k in range(1, 7):
    plus = 2**(2*k-1) + 2**(k-1) - 1; minus = 2**(2*k-1) - 2**(k-1) - 1
    c = count(k)
    print(f"k={k}: singular vectors {c}; O+ would be {plus}, O- would be {minus}; type = {'+' if c==plus else '-'}; (-1)^k = {'+' if k%2==0 else '-'}")
