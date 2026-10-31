"""Equivariant orbit reduction of a seed with a free cyclic group (c2).
Remove one tau-orbit on side A and one on side B (tau of order h, orbits of size h), then rewire the loose
slots by a tau-equivariant perfect matching. Candidates are scored by ./shrink stream (far per graph)."""
import sys, json, subprocess, itertools, random
from collections import defaultdict
seed, autf, h, outprefix = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
maxcand = int(sys.argv[5]) if len(sys.argv) > 5 else 10**9
L = open(seed).read().split(); n = int(L[0])
E = [(int(L[i]), int(L[i+1])) for i in range(1, len(L), 2)]
nbr = defaultdict(list)
for a, b in E: nbr[a].append(b); nbr[b].append(a)
# sides by BFS
side = {0: 0}; q = [0]
for x in q:
    for y in nbr[x]:
        if y not in side: side[y] = 1 - side[x]; q.append(y)
auts = json.load(open(autf))
def comp(p, q_): return [p[q_[i]] for i in range(n)]
def order(p):
    k = 1; cur = p[:]
    while cur != list(range(n)): cur = comp(p, cur); k += 1
    return k
# find an automorphism of order exactly h (cyclic group element)
tau = None
for p in auts:
    if order(p) == h and all(side[p[v]] == side[v] for v in range(n)) and all(p[v] != v for v in range(n)):
        tau = p; break
assert tau is not None, "no automorphism of order %d" % h
def tpow(v, j):
    for _ in range(j % h): v = tau[v]
    return v
# tau orbits
seen = set(); orbs = []
for v in range(n):
    if v in seen: continue
    o = [v]; seen.add(v); w = tau[v]
    while w != v: o.append(w); seen.add(w); w = tau[w]
    orbs.append(o)
A_orbs = [o for o in orbs if side[o[0]] == 0]
B_orbs = [o for o in orbs if side[o[0]] == 1]
print("orbits: A", len(A_orbs), "B", len(B_orbs), "size", h, file=sys.stderr)
Eset = set((min(a, b), max(a, b)) for a, b in E)
def slots_orbits(S_removed, other_removed_side_rep):
    pass
def candidates():
    for OA in A_orbs:
        SA_ = set(OA)
        for OB in B_orbs:
            SB_ = set(OB)
            S = SA_ | SB_
            # slots: A-side slots (x, s): x outside in A, s in OB ; B-side slots (y, t): y outside in B, t in OA
            Aslots = [(x, s) for s in OB for x in nbr[s] if x not in S]
            Bslots = [(y, t) for t in OA for y in nbr[t] if y not in S]
            if len(Aslots) != len(Bslots) or len(Aslots) % h != 0: continue
            k = len(Aslots) // h
            # orbits of slots under tau
            def orbit_reps(slots):
                seen_s = set(); reps = []
                for sl in slots:
                    if sl in seen_s: continue
                    reps.append(sl); x, s = sl
                    for j in range(h): seen_s.add((tpow(x, j), tpow(s, j)))
                return reps
            Ar = orbit_reps(Aslots); Br = orbit_reps(Bslots)
            assert len(Ar) == k and len(Br) == k, (len(Ar), len(Br), k)
            for perm in itertools.permutations(range(k)):
                for offs in itertools.product(range(h), repeat=k):
                    newe = []
                    for i in range(k):
                        x, s = Ar[i]; y, t = Br[perm[i]]
                        for j in range(h):
                            # slot tau^j(x,s) matched with tau^(j+off) (y,t)
                            newe.append((tpow(x, j), tpow(y, j + offs[i])))
                    # validate: no existing edge, no duplicates
                    ok = True; used = set()
                    for (x, y) in newe:
                        if (min(x, y), max(x, y)) in Eset or (x, y) in used: ok = False; break
                        used.add((x, y))
                    if not ok: continue
                    yield OA, OB, S, newe

def build(S, newe):
    keep = [v for v in range(n) if v not in S]
    mp = {v: i for i, v in enumerate(keep)}
    edges = [(mp[a], mp[b]) for a, b in E if a not in S and b not in S]
    edges += [(mp[x], mp[y]) for x, y in newe]
    return len(keep), edges

proc = subprocess.Popen(['./shrink', 'stream'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
results = []
cnt = 0
meta = []
batch = []
def flush_batch():
    global batch
    if not batch: return
    data = ''.join(f"{nn} {len(ed)}\n" + ''.join(f"{a} {b}\n" for a, b in ed) for nn, ed, _ in batch)
    proc.stdin.write(data); proc.stdin.flush()
    for nn, ed, info in batch:
        line = proc.stdout.readline().strip()
        results.append((int(line) if line.lstrip('-').isdigit() else 10**9, info))
    batch = []
for OA, OB, S, newe in candidates():
    if cnt >= maxcand: break
    nn, ed = build(S, newe)
    batch.append((nn, ed, (tuple(OA), tuple(OB), tuple(newe))))
    cnt += 1
    if len(batch) >= 500: flush_batch()
flush_batch()
proc.stdin.close(); proc.wait()
results.sort(key=lambda r: r[0])
print("candidates", len(results), "best far", results[0][0] if results else None, file=sys.stderr)
from collections import Counter
print("far histogram (lowest 15):", sorted(Counter(r[0] for r in results).items())[:15])
# write best few
for rank, (f, info) in enumerate(results[:3]):
    OA, OB, newe = info
    S = set(OA) | set(OB)
    nn, ed = build(S, list(newe))
    fn = f"{outprefix}_rank{rank}_far{f}.edges"
    with open(fn, 'w') as fo:
        fo.write(f"{nn}\n" + ''.join(f"{a} {b}\n" for a, b in ed))
    print("wrote", fn)
