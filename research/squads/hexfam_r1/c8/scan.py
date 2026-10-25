import sys, time, random, json, numpy as np
sys.path.insert(0,'/home/user/degree-diameter/research/squads/hexfam_r1/c8')
sys.path.insert(0,'/home/user/degree-diameter/research/projects/hexagon-family/tools')
from chart import *
from mwc import max_weight_clique
q = int(sys.argv[1]); seed = int(sys.argv[2]); T = int(sys.argv[3]); olo, ohi = int(sys.argv[4]), int(sys.argv[5])
tl = float(sys.argv[6]) if len(sys.argv) > 6 else 10.0
ch = Chart(q); rng = random.Random(seed); nrng = np.random.default_rng(seed)
best_overall = (0, None)
t0 = time.time()
log = open(f'scan_q{q}_s{seed}.jsonl', 'a')
for tr in range(T):
    M = ch.random_orthogonal(rng, nref=rng.randint(2, 6))
    o = matpow_order(M, q)
    if o is None or o < olo or o > ohi: continue
    lam = rng.randrange(1, q)
    M2 = (lam * M) % q
    label, size, ov = cyc_orbits(ch, M2, np.zeros(5, dtype=np.int64))
    if ov.sum() == 0: continue
    vids, A = orbit_graph(ch, label, size, ov)
    w = size[vids].astype(np.int64)
    adj = []
    for i in range(len(vids)):
        bits = 0
        nb = np.nonzero(A[i])[0]
        for j in nb: bits |= (1 << int(j))
        adj.append(bits)
    tot, verts, exact = max_weight_clique(list(map(int, w)), adj, tlimit=tl)
    # orbit members -> chart points
    members = []
    order = np.argsort(label, kind='stable'); starts = np.concatenate([[0], np.cumsum(size)[:-1]])
    for v in verts:
        o_id = vids[v]
        members.append(order[starts[o_id]:starts[o_id] + size[o_id]])
    pts = np.concatenate(members) if members else np.array([], dtype=np.int64)
    rec = dict(order=o, lam=lam, nvalid=len(vids), density=round(float(A.mean()), 3), total=int(tot), exact=bool(exact), t=round(time.time()-t0))
    print(json.dumps(rec), flush=True); log.write(json.dumps(rec)+'\n'); log.flush()
    if tot > best_overall[0]:
        best_overall = (tot, pts.tolist(), M2.tolist(), o, lam)
        np.save(f'best_orb_q{q}_s{seed}.npy', pts)
print('BEST', best_overall[0], best_overall[3], best_overall[4], flush=True)
