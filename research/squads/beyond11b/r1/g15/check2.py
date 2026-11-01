# Exact checks for the -I lemma (f = 0). Enumerate pair-sequences explicitly for small h.
import random, sys, itertools
from check import *   # reuses group, alpha, random_S, mI, idx, e
h = int(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]); seed = int(sys.argv[4])
rng = random.Random(seed)
def prod_seq(seq, S):
    g = e
    for (s,t) in seq:
        g = mul(g, mul(inv(s), t))
    return g
def rot(seq): return seq[1:] + seq[:1]           # rotate blocks by one pair
def rev(seq): return tuple((t, s) for (s, t) in reversed(seq))   # reversal + inversion of blocks
def al(seq): return tuple((alpha(s), alpha(t)) for (s, t) in seq)
ok_rot = ok_rev = ok_al = ok_prod = 0; tot_ok = 0; bad3 = 0; bad2 = 0; maxorb = 0
for tr in range(trials):
    S = random_S(m, rng)
    Sset = set(S)
    seqs = [tuple(x) for x in itertools.product([(s,t) for s in S for t in S], repeat=h)]
    Ssub = [seq for seq in seqs if prod_seq(seq, S) == mI]
    SS = set(Ssub)
    # invariance of the -I set under the generators of D_h x Z_3
    closed = all(rot(q) in SS and rev(q) in SS and al(q) in SS for q in Ssub)
    tot_ok += closed
    c = len(Ssub)
    if c % 3: bad3 += 1
    # reversal-fixed sequences with product -I, parity check
    fixrev = sum(1 for q in Ssub if rev(q) == q)
    if (c - fixrev) % 2: bad2 += 1
    # orbit sizes under <rot, rev, al> (orbit by BFS over the group action)
    seen = set(); orbs = []
    for q in Ssub:
        if q in seen: continue
        orb = {q}; st = [q]
        while st:
            x = st.pop()
            for y in (rot(x), rev(x), al(x)):
                if y not in orb: orb.add(y); st.append(y)
        seen |= orb; orbs.append(len(orb))
    if orbs: maxorb = max(maxorb, max(orbs))
    print(f"trial {tr}: #seq(-I)={c} orbits={sorted(orbs)} closed={closed} fixed_by_rev={fixrev}")
print(f"h={h} Delta={3*m} trials={trials}: closed under D_h x Z_3 in {tot_ok}/{trials}; count%3!=0 in {bad3}; (count - #revfixed) odd in {bad2}; max orbit {maxorb} (6h={6*h})")
