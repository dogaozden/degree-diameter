# requot: re-express a lift over G (flift convention (u,x)~(v,g x)) as a lift over subgroup H (index r).
# Outputs: H table .bin (int32 h, uint16 table, identity 0), base file "k' E'" + edges, and voltages in flift convention.
import sys, os
sys.path.insert(0, "/home/user/degree-diameter/research/squads/own-small/r1/a1/work")
from common import *
import pickle

N, M = load_group()
INV = inverses(N, M)
SUBS = {tuple(k): v for k, v in pickle.load(open("/home/user/degree-diameter/research/squads/own-small/r1/a1/work/subs.pkl", "rb")).items()}

def sub_by_order_index(h, which=0):
    cands = [k for k in SUBS if len(k) == h]
    return cands[which]

def make_H(Hset):
    H = sorted(Hset, key=lambda x: (x != 0, x))
    pos = {x: j for j, x in enumerate(H)}
    h = len(H)
    MH = np.array([[pos[int(M[x, y])] for y in H] for x in H], dtype=np.int64)
    return H, pos, h, MH

def requot_base(k, edges, volts_left, Hset):
    """volts_left: G voltages in flift (left) convention. Returns (kk, newedges, voltH_left_per_newedge_order)."""
    H, pos, h, MH = make_H(Hset)
    # right-convention voltages a = inv(g); coset reps t of right cosets Ht
    coset_of = {}; reps = []
    for g in range(N):
        if g in coset_of: continue
        j = len(reps); reps.append(g)
        for x in H: coset_of[int(M[x, g])] = (j, x)
    r = len(reps); p = k // 2
    newE = []
    for (u, v), g in zip(edges, volts_left):
        a = INV[g]                       # right convention (u,y)~(v,y*a)
        for j, t in enumerate(reps):
            kk, bb = coset_of[int(M[t, a])]  # t*a = bb*t_kk
            newE.append((u * r + j, v * r + kk, pos[bb]))   # right convention, H-element bb
    return k * r, h, MH, pos, newE

def flift_edges_from(newE, h, MH, kk):
    """Convert right-convention H-lift (u,y)~(v,y*b) to flift left convention voltages (inverse)."""
    raise NotImplementedError

if __name__ == "__main__":
    pass
