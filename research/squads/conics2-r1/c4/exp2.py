import sys, random, subprocess, numpy as np, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c4')
from build3 import read_sol, build, write_edges, HEX
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
from hexload import load
q, N, LP, PL, X = load(HEX)
SOL = '/home/user/degree-diameter/research/frontier/sols/d7D7_hex5_mirror81_n23598.sol'
_, _, R0, hub0, K0, _, sig = read_sol(SOL)

def add_hub_pair(hub, K, rng):
    """add line hub K and point hub K via 2 double-switches; keeps bipartite simple, degrees 4"""
    hub = set(hub)
    A, B = K, K
    for _ in range(2):
        e1, e2 = rng.sample(sorted(hub), 2)
        (a1, b1), (a2, b2) = e1, e2
        if a1 == a2 or b1 == b2: continue
        if (A, b1) in hub or (A, b2) in hub or (a1, B) in hub or (a2, B) in hub: continue
        hub.discard(e1); hub.discard(e2)
        hub |= {(A, b1), (A, b2), (a1, B), (a2, B)}
    return sorted(hub)

def hubdist_ok(hub, K):
    adj = collections.defaultdict(list)
    for a, b in hub: adj[('L', a)].append(('P', b)); adj[('P', b)].append(('L', a))
    worst = 0
    for t in range(K):
        d = {('L', t): 0}; dq = collections.deque([('L', t)])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in d: d[y] = d[x] + 1; dq.append(y)
        for u in range(K):
            if ('L', u) in d: worst = max(worst, d[('L', u)])
            else: return 99
    return worst

def count(R, hub, K, tag):
    n, E = build(q, N, LP, sig, R, hub, K, K)
    fn = f'/home/user/degree-diameter/research/squads/conics2-r1/c4/tmp_{tag}.edges'
    write_edges(fn, n, E)
    out = subprocess.run(['./count7', fn, '7'], capture_output=True, text=True).stdout.strip()
    subprocess.run(['rm', '-f', fn])
    return out

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    print('K=81 record:', count(R0, hub0, K0, 'rec'))
    hubK = add_hub_pair(hub0, K0, rng)
    print('K=82 hub degrees ok?', hubdist_ok(hubK, K0 + 1))
    cand = [p for p in range(N) if p not in set(R0)]
    rng.shuffle(cand)
    res = []
    for x0 in cand[:12]:
        R1 = R0 + [x0]
        out = count(R1, hubK, K0 + 1, f'{x0}')
        res.append((x0, out))
        print(x0, out, flush=True)
