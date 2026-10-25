"""Bipartite flag graphs of spherical buildings (generalising C(k,q) of Cames van Batenburg-Korsky).
Building of rank r, Coxeter diagram bipartitioned I1 | I2 (each part pairwise commuting).  Vertices: partial flags of
type I1 and of type I2; adjacent iff together a chamber.  Degree of an I1-flag = prod over I2 of (panel size).
Equal parameters q and |I1| = |I2| = r/2: (q+1)^(r/2)-regular, order 2 #chambers/(q+1)^(r/2),
#chambers = prod_i [d_i]_q (d_i = degrees of W), diameter = Coxeter number h = max d_i (w0 = (c1 c2)^(h/2) for a
bipartite Coxeter element; every w <= w0 is a subword of that block word, so <= h block steps; w0 needs h).
Checked by computer: A_4, q=2,3 (flags.py: diameter 5) and C_4, q=2 (cflags.py: diameter 8).
Prints order, Moore bound and ratio, and the table value where Δ <= 16, D <= 10."""
import sys
sys.path.insert(0, '../frontier')
from heuristic import TABLE, moore
TYPES = {'A2': [2, 3], 'A4': [2, 3, 4, 5], 'A6': [2, 3, 4, 5, 6, 7], 'A8': list(range(2, 10)),
         'C2': [2, 4], 'C4': [2, 4, 6, 8], 'C6': [2, 4, 6, 8, 10, 12], 'G2': [2, 6], 'F4': [2, 6, 8, 12],
         'E6': [2, 5, 6, 8, 9, 12], 'E8': [2, 8, 12, 14, 18, 20, 24, 30]}
def qint(d, q): return sum(q ** i for i in range(d))
print("type | q | D=h | Δ | vertices | bipartite Moore | ratio | table (if Δ<=16, D<=10)")
for t, degs in TYPES.items():
    r = len(degs); h = max(degs)
    for q in (2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 32, 64):
        ch = 1
        for d in degs: ch *= qint(d, q)
        Delta = (q + 1) ** (r // 2)
        if Delta > 10 ** 6: continue
        V = 2 * ch // (q + 1) ** (r // 2)
        M = moore(Delta, h)
        tab = TABLE[Delta][h - 3] if Delta <= 16 and 3 <= h <= 10 else None
        print(f"{t} | {q} | {h} | {Delta} | {V:,} | {M:,} | {V/M:.4f} | {tab if tab else ''}{'  <-- above table' if tab and V > tab else ''}")
