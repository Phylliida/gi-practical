#!/usr/bin/env python3
"""Numbers along the trace of docs/w47-mu.md section 3, and the orbital check at m=6."""
import math, sys

def gl(k):
    r = 1
    for i in range(k):
        r *= 2**k - 2**i
    return r

def gaussian2(k):           # number of 2-subspaces of F_2^k
    return (2**k - 1) * (2**(k-1) - 1) // 3

print("m  log2 n  log2 N  |W|/n     d/n     log2|P|  (log2|P|)/(log2 N)^2  mu=log|P|/log d  ratio to log2 N")
for m in list(range(5, 13)) + [20, 64, 128, 214]:
    pts = 2**m - 1; lines = gaussian2(m); n = pts + lines
    N = n * (n - 1)
    W = (2**m - 4) * (2**m - 8) // 6
    d = gaussian2(m - 2)
    lgP = math.log2(gl(m - 2))
    lgN = math.log2(N)
    print(f"{m:3d} {math.log2(n):7.2f} {lgN:7.2f} {W/n:7.4f} {d/n:8.4f} {lgP:9.1f} "
          f"{lgP/lgN**2:11.4f} {lgP/math.log2(d):11.2f} {lgP/math.log2(d)/lgN:8.4f}")

print("\n|O_gen|/|W| versus non-generic per w, and the largest-orbit condition:")
for m in range(6, 12):
    W = (2**m - 4) * (2**m - 8) // 6
    gen = (2**m - 16) * (2**m - 32) // 6
    pts = 2**m - 1; lines = gaussian2(m); n = pts + lines
    nonW = n - W
    print(f"m={m}: |W|={W} generic per w={gen} rest of W={W-1-gen} |Gamma\\W|={nonW} "
          f"O_gen largest: {gen > W-1-gen and gen > nonW}")
