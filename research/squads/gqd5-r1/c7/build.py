"""Card c7: q=5, r=2, five levels, types H H D H D on the rotational tournament j->j+1, j->j+2 (mod 5).
Transition (j,k) goes from level j to level (j+k)%5.
Friendly H->D: identity on points, freed = ovoid of Q(4,5).  Friendly D->H: identity on lines, freed = partial ovoid of
W(5) (= partial spread of Q(4,5)).  Non-friendly H->H and D->D: identity index map, nothing freed.
Hubs: K_B = K_A = min out-cap = min in-cap = 21. Hub graph Y: random 3-regular bipartite (degree q-r = 3)."""
import sys, json, random, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import Q4
from levels import build, write_edges

TYPES = list('HHDHD')
NL, R_ = 5, 2
G = Q4(5)
NP = G.np  # 156


def freed_sets(O_a, O_b, P_a, P_b):
    """transition (j,k) -> freed set. Arcs: (0,2) H->D, (1,1) H->D, (2,1) D->H, (3,1) H->D, (4,1) D->H, (4,2) D->H."""
    R = {(j, k): [] for j in range(NL) for k in (1, 2)}
    R[(0, 2)] = O_a
    R[(1, 1)] = O_b
    R[(2, 1)] = P_a
    R[(3, 1)] = O_a
    R[(4, 1)] = P_a
    R[(4, 2)] = P_b
    return R


def pick_distinct(lst, key, k, rng):
    """k entries of lst (random order) whose key values are pairwise distinct"""
    lst = lst[:]; rng.shuffle(lst)
    out, seen = [], set()
    for x in lst:
        if key(x) not in seen:
            seen.add(key(x)); out.append(x)
            if len(out) == k:
                return out
    raise ValueError('not enough distinct slots')


def run(seed, out_path, O_a=None, O_b=None, P_a=None, P_b=None):
    rng = random.Random(seed)
    ident = list(range(NP))
    M = {(j, k): ident for j in range(NL) for k in (1, 2)}
    R = freed_sets(O_a, O_b, P_a, P_b)
    A_slot = {j: [] for j in range(NL)}   # level j -> list of (t, a)  (freed A-elements of level j)
    B_slot = {j: [] for j in range(NL)}   # level j -> list of (t, a)  (freed pairs whose B-end lies in level j)
    for (j, k), Rt in R.items():
        for a in Rt:
            A_slot[j].append(((j, k), a))
            B_slot[(j + k) % NL].append(((j, k), a))
    KB = min(len(A_slot[j]) for j in range(NL))
    KA = min(len(B_slot[j]) for j in range(NL))
    # B-hubs: one A-slot per level, distinct elements (random injection per level)
    Bh = [[None] * NL for _ in range(KB)]
    for j in range(NL):
        sl = pick_distinct(A_slot[j], lambda x: x[1], KB, rng)
        for h in range(KB):
            t, a = sl[h]
            Bh[h][j] = (j, a, t)
    # A-hubs: one B-slot per level; B-element = M[t](a)
    Ah = [[None] * NL for _ in range(KA)]
    for j in range(NL):
        sl = pick_distinct(B_slot[j], lambda x: M[x[0]][x[1]], KA, rng)
        for g in range(KA):
            t, a = sl[g]
            Ah[g][j] = (j, M[t][a], t)
    # hub graph Y: union of 3 random perfect matchings between B-hubs and A-hubs, no repeated pair
    while True:
        E = set()
        for _ in range(3):
            perm = list(range(KA)); rng.shuffle(perm)
            for h in range(KB):
                E.add((h, perm[h]))
        if len(E) == 3 * KB:
            break
    Y = sorted(E)
    types = TYPES
    n, edges = build(G, types, M, R=R, Bhubs=Bh, Ahubs=Ah, Y=Y)
    write_edges(out_path, n, edges)
    return n, KA, KB, {k: len(v) for k, v in R.items() if v}


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, 'best.edges')
    n, KA, KB, info = run(seed, out)
    print('n', n, 'KA', KA, 'KB', KB, 'R sizes', info)
