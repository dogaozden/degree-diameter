"""(3) Coverage: for a given delta, which balanced K in 1..Kmax are reached by verified hub graphs.
Method A: random maximal K+K graphs with max degree <= delta (up to 10 seeds per K).
Method B: greedy vertex-pair deletion from the explicit level graph W(q), r = delta-q-1 (verified after every step)."""
import sys, json, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c10')
from lib import *
import gqlib
delta = int(sys.argv[1]); mode = sys.argv[2]
out = {'delta': delta, 'mode': mode}
if mode == 'random':
    kmax = int(sys.argv[3])
    reached = {}
    fails = []
    for K in range(1, kmax + 1):
        ok = None
        for t in range(10):
            rng = random.Random(K * 7919 + t)
            e = random_maximal_bip(K, K, delta, rng)
            if K <= delta:
                e = [(a, K + b) for a in range(K) for b in range(K)]
            res = check(2 * K, e)
            if res.get('valid') == 1:
                ok = t; break
        if ok is None: fails.append(K)
        else: reached[K] = ok
    out['random_reached_count'] = len(reached)
    out['random_fail_list'] = fails[:50]
    out['random_fail_count'] = len(fails)
    out['random_max_contiguous_from_1'] = next((k - 1 for k in range(1, kmax + 2) if k not in reached), kmax)
    print(json.dumps(out), flush=True)
elif mode == 'delete':
    q = int(sys.argv[3]); r = delta - q - 1
    G = gqlib.W(q)
    rng = random.Random(12345)
    n, E, nA, nB = level_graph(G, r, rng)
    # colour by BFS
    adj = [[] for _ in range(n)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    col = [-1] * n; col[0] = 0; st = [0]
    while st:
        v = st.pop()
        for w in adj[v]:
            if col[w] < 0: col[w] = 1 - col[v]; st.append(w)
    A = [v for v in range(n) if col[v] == 0]; B = [v for v in range(n) if col[v] == 1]
    alive_A = set(A); alive_B = set(B)
    K = len(A)
    reached = [K]
    assert len(A) == len(B) == nA
    Eset = E
    # verify start
    def graph_of(aA, aB):
        idA = {v: i for i, v in enumerate(sorted(aA))}
        idB = {v: len(idA) + i for i, v in enumerate(sorted(aB))}
        ids = {**idA, **idB}
        ed = [(ids[u], ids[v]) for u, v in Eset if u in ids and v in ids]
        return len(ids), ed
    n0, e0 = graph_of(alive_A, alive_B)
    print("start", check(n0, e0), flush=True)
    failures_in_row = 0
    TRIES = int(sys.argv[4]) if len(sys.argv) > 4 else 15
    last_ok = None
    while len(alive_A) > 1:
        done = False
        for t in range(TRIES):
            a = rng.choice(sorted(alive_A)); b = rng.choice(sorted(alive_B))
            tA = alive_A - {a}; tB = alive_B - {b}
            nn, ee = graph_of(tA, tB)
            res = check(nn, ee)
            if res.get('valid') == 1:
                alive_A, alive_B = tA, tB
                reached.append(len(alive_A)); done = True; break
        if not done:
            break
    out['delete_start_K'] = K
    out['delete_reached_K_min'] = min(reached)
    out['delete_reached_count'] = len(reached)
    out['delete_stopped_at_K'] = len(alive_A)
    out['delete_final_edges_check'] = check(*graph_of(alive_A, alive_B))
    # the set of reached K values is the contiguous range [min, K] (each step verified)
    json.dump({'reached_min': min(reached), 'reached_max': K, 'contiguous': True}, open(f'delete_d{delta}_q{q}.json', 'w'))
    print(json.dumps(out), flush=True)
