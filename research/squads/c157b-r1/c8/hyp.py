#!/usr/bin/env python3
"""hyp.py: for hyperplanes Sigma = {p : B(x,p)=0}, count points of H in Sigma, H-lines inside Sigma, free points."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/c157b-r1/c8')
from geom import load, pl_table, q
N, L, LP, C = load()
PL = pl_table(N, L, LP)
# bilinear form of Q: B(p,r) = p0 r4 + p4 r0 + p1 r5 + p5 r1 + p2 r6 + p6 r2 - 2 p3 r3
def Bvec(x):
    # returns coefficient vector c with B(x,p) = c . p
    c = np.zeros(7, dtype=np.int64)
    c[4] = x[0]; c[0] = x[4]; c[5] = x[1]; c[1] = x[5]; c[6] = x[2]; c[2] = x[6]; c[3] = -2 * x[3]
    return c % q
def analyse(x, name):
    c = Bvec(np.array(x))
    val = (C @ c) % q
    inS = (val == 0)
    nS = int(inS.sum())
    inside = inS[LP].all(axis=1)
    Lin = int(inside.sum())
    # inside lines through each point
    t = np.zeros(N, dtype=np.int64)
    ins_idx = np.nonzero(inside)[0]
    np.add.at(t, LP[ins_idx].reshape(-1), 1)
    F = int((inS & (t == 0)).sum())
    tdist = np.bincount(t[inS], minlength=13)
    print(f'{name}: |Sigma∩H|={nS}  inside-lines={Lin}  free(t=0)={F}  t-distribution={tdist.tolist()}', flush=True)
    return inS, inside, t
if __name__ == '__main__':
    analyse([0,0,0,1,0,0,0], 'a=0 (x=e3, Q(x)=-1)')
    analyse([1,0,0,0,1,0,0], 'x=e0+e4 (Q(x)=1)')
    analyse([1,0,0,0,0,0,0], 'x=e0 (tangent)')
