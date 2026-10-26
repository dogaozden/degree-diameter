"""c12 hub surgery on the Z_10 lemma lift (sigma1 voltage 1, sigma2 voltage 4).
Stage 1: greedy (chunked, bisecting) choice of matching-edge ORBITS (each orbit = one base matching edge in all 10
copies) whose deletion keeps diameter <= 8, checked exactly with gcheck from copy-0 sources.
Stage 2: hub representatives (orbits of new vertices) of degree t, each joined to t freed slots of t distinct
base vertices of one colour (A-hubs: freed points, colour line; B-hubs: freed lines, colour point), then gcheck again.
Usage: surgery.py q seed budget_checks"""
import sys, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c12')
from lift import make_base, gcost
import numpy as np

q = int(sys.argv[1]); seed = int(sys.argv[2]); budget = int(sys.argv[3])
N, base_hex, match, s1, s2 = make_base(q, seed)
S0 = 2 * N
cands = match  # index c: (point p, line N+y, shift a); candidate c in [0, 2N): first N use sigma1, next N sigma2
deleted = set()
checks = 0
t0 = time.time()

def edges_for(dels, hubs=()):
    """hubs: list of (type, [base vertex ids]) with type 'A' (colour line, joined to points) or 'B' (colour point)."""
    E = list(base_hex)
    E += [cands[c] for c in range(len(cands)) if c not in dels]
    for h, (typ, vs) in enumerate(hubs):
        for v in vs:
            E.append((S0 + h, v, 0))
    return E

def ok(dels, hubs=(), tag='s'):
    global checks
    checks += 1
    S = S0 + len(hubs)
    bad, msg = gcost(S, edges_for(dels, hubs), 8, f'q{q}{tag}')
    return bad == 0, bad

def try_add(group):
    """Try to delete all candidates in group (on top of deleted). Bisect on failure. Returns number accepted."""
    global deleted
    if checks >= budget or not group:
        return 0
    trial = deleted | set(group)
    good, bad = ok(trial, tag='del')
    if good:
        deleted = trial
        return len(group)
    if len(group) == 1:
        return 0
    h = len(group) // 2
    return try_add(group[:h]) + try_add(group[h:])

order = list(range(len(cands)))
random.Random(seed).shuffle(order)
chunk = max(1, len(order) // 16)
i = 0
while i < len(order) and checks < budget:
    got = try_add(order[i:i + chunk])
    i += chunk
    print(f'chunk done i={i} accepted_total={len(deleted)} checks={checks} t={time.time()-t0:.0f}s', flush=True)
print(f'STAGE1 q={q} seed={seed} deleted_orbits={len(deleted)} of {len(cands)} checks={checks}', flush=True)

# Stage 2: freed slots
dels_sorted = sorted(deleted)
freeP = [cands[c][0] for c in dels_sorted]            # base point ids (copy 0 reps)
freeL = [cands[c][1] for c in dels_sorted]            # base line ids
results = []
for t in sorted({2, 3, q + 3}):
    rng = random.Random(seed + t)
    for typ, pool in (('A', freeP), ('B', freeL)):
        pool = pool[:]
        rng.shuffle(pool)
        hubs = []
        used = set()
        for v in pool:
            if v in used: continue
            used.add(v)
            hubs.append(v)
        # group into hubs of degree t with distinct vertices (leftover dropped)
        groups = [hubs[j:j + t] for j in range(0, len(hubs) - t + 1, t)]
        if not groups: continue
        hub_list = [(typ, g) for g in groups]
        good, bad = ok(deleted, hub_list, tag='hub')
        print(f'hubs t={t} type={typ} n_hub_reps={len(groups)} gain_vertices={10*len(groups)} valid={good} bad={bad} checks={checks}', flush=True)
        results.append((t, typ, len(groups), good))
print('RESULTS', results)
