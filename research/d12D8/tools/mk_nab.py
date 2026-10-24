"""Non-abelian 'bounce' test: H(q) + one incidence matching M tripled (copies: e, a, b fixed group elements),
unmatched hexagon edges random group elements (or 'none' = identity). Writes liftcheck table format.
usage: mk_nab.py q GROUP mode seed out   mode: rnd (random everywhere) | bnc (copies fixed e,a,b; others random)"""
import sys, random
sys.path.insert(0, '.')
from hexlib import load_hex
from groups import by_name, table
import importlib.util
spec = importlib.util.spec_from_file_location('mkv', 'mk_var.py')
q, gname, mode, seed, out = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
random.seed(seed)
n, lines = load_hex(q)
elems, idx = by_name(gname); T = table(elems, idx); m = len(elems)
# incidence matching (copied logic from mk_var.py)
pl = [[] for _ in range(n)]
for l in range(n):
    for p in lines[l]: pl[p].append(l)
import collections
def inc_matching():
    order = list(range(n)); random.shuffle(order)
    matchL = [-1] * n; matchP = [-1] * n
    adj = [random.sample(pl[p], len(pl[p])) for p in range(n)]
    for p in order:
        for l in adj[p]:
            if matchL[l] < 0: matchL[l] = p; matchP[p] = l; break
    for p0 in [p for p in range(n) if matchP[p] < 0]:
        prev = {}; dq = collections.deque([p0]); seen = set(); found = None
        while dq and found is None:
            p = dq.popleft()
            for l in adj[p]:
                if l in seen: continue
                seen.add(l); prev[l] = p
                if matchL[l] < 0: found = l; break
                dq.append(matchL[l])
        l = found
        while l is not None:
            p = prev[l]; nl = matchP[p]; matchP[p] = l; matchL[l] = p; l = nl if nl != -1 else None
    return matchP
M = inc_matching()
# fixed bounce elements: pick a, b "generic": a = random non-identity, b = random not in {e, a}
a = random.randrange(1, m); b = random.choice([x for x in range(1, m) if x != a])
E = []
for l in range(n):
    for p in lines[l]:
        p = int(p)
        if M[p] == l:
            if mode == 'bnc':
                E += [(p, l, 0), (p, l, a), (p, l, b)]
            else:
                E += [(p, l, random.randrange(m)) for _ in range(3)]
        else:
            E.append((p, l, random.randrange(m)))
with open(out, 'w') as f:
    f.write(f"{n} {n} {m} table\n")
    for row in T: f.write(' '.join(map(str, row)) + '\n')
    for p, l, g in E: f.write(f"{p} {l} {g}\n")
print(gname, m, 'a,b =', a, b)
