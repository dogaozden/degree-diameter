#!/usr/bin/env python3
"""mkhubF.py IN.sol "FDSET" OUT.sol [SEED]: H=2 dmhub state -> H=3-numbered state for per-flag FLAGDEL.  Keeps every
original hub edge (hub t of flag i -> index 3i+t); for each flag in FDSET (third hub per side), makes every one of its
6 hubs adjacent to a hub of the other side of the SAME flag (needed to reroute the deleted flag edge), dropping an
inter-flag edge of a full hub when necessary (one whose flag pair is also realised by another edge, if possible),
then fills the free slots of the new hubs with inter-flag edges to new flag pairs."""
import sys, random, collections
import lns
S = lns.read_sol(sys.argv[1]); fd = set(int(x) for x in sys.argv[2].split()); out = sys.argv[3]
rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
F = S['F']; k = len(F); H0 = S['H']; assert H0 == 2; H = 3
hg = [int(x) for x in S['rows']['hubgraph']]
E = set((H * (hg[e] // 2) + hg[e] % 2, H * (hg[e + 1] // 2) + hg[e + 1] % 2) for e in range(0, len(hg), 2))
on = lambda h: h % H < 2 or h // H in fd
def degA(a): return sum(1 for x, y in E if x == a)
def degB(b): return sum(1 for x, y in E if y == b)
def pairs(): return collections.Counter((x // H, y // H) for x, y in E)
def drop_from(h, side):
    """drop one inter-flag edge at hub h (side 'A' line-side, 'B' point-side), preferring duplicated flag pairs"""
    pc = pairs(); cand = [(x, y) for x, y in E if (x if side == 'A' else y) == h and x // H != y // H]
    cand.sort(key=lambda e: -pc[(e[0] // H, e[1] // H)])
    if cand: E.discard(cand[0]); return True
    return False
for i in sorted(fd):
    for t in range(H):
        a = H * i + t
        if not any(x == a and y // H == i for x, y in E):
            b = min((H * i + u for u in range(H)), key=lambda b: degB(b))
            if degA(a) >= 4: drop_from(a, 'A')
            if degB(b) >= 4: drop_from(b, 'B')
            E.add((a, b))
        b = H * i + t
        if not any(y == b and x // H == i for x, y in E):
            a2 = min((H * i + u for u in range(H)), key=lambda a2: degA(a2))
            if degA(a2) >= 4: drop_from(a2, 'A')
            if degB(b) >= 4: drop_from(b, 'B')
            E.add((a2, b))
# fill free slots of enabled hubs with edges creating new flag pairs (then any pairs)
for rnd_ in range(2):
    hubsA = [a for a in range(H * k) if on(a)]; hubsB = [b for b in range(H * k) if on(b)]
    rng.shuffle(hubsA)
    for a in hubsA:
        while degA(a) < 4:
            pc = pairs()
            cands = [b for b in hubsB if degB(b) < 4 and (a, b) not in E and b // H != a // H and (rnd_ == 1 or pc[(a // H, b // H)] == 0)]
            if not cands: break
            E.add((a, rng.choice(cands)))
rows = S['rows']; rows['dmhub'] = rows['dmhub'][:]; rows['dmhub'][3] = '3'
rows['hubgraph'] = [str(x) for ab in sorted(E) for x in ab]
lns.write_sol(out, S, S['sig'], -1)
bad = [h for h in range(H * k) if on(h) and (degA(h) > 4 or degB(h) > 4)]
print('hub edges', len(E), 'over-full hubs', bad, 'flag pairs', len(pairs()))
