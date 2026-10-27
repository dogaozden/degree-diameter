"""Fraction of points t with g(t) perpendicular to t (hexagon distance <= 4): random G_2(q) elements vs a long root elation."""
import sys, random, numpy as np
sys.path.insert(0,'.')
from geo import Hex
from mktwist import rand_elem
for q in [3,4,5,7]:
    H=Hex(f'hex_q{q}.txt'); F=H.F; rng=random.Random(5)
    # perp test via hexagon distance: d(t,gt)<=4  <=> B(t,gt)=0 (odd q) ; use B for all q (polar form), check vs BFS on small q
    def frac(M):
        Y=H.normalize(F.mm(H.P, M.T)); b=np.array([H.B(H.P[i],Y[i]) for i in range(H.n)]); return (b==0).mean()
    fr=[frac(rand_elem(H,rng,12)) for _ in range(6)]
    l0=H.L[5]; e=H.siegel(H.P[l0[0]],H.P[l0[1]])
    print(f"q={q}: random G2 elements: fraction of t with gt perp t = {[round(x,3) for x in fr]} (1/q = {1/q:.3f}); long root elation: {frac(e):.3f}")
