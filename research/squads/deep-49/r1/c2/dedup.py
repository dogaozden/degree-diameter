# Invariant classes of the candidate groups (numpy: element-order distribution, centre size, q), then
# pairs inside a class are sent to GAP IsomorphismGroups (iso_pairs.g). Writes runs/classes.json.
import json, collections
import numpy as np
rows = [l.split() for l in open('/home/user/degree-diameter/research/squads/deep-49/r1/c2/runs/cands.txt') if l.strip()]
q_of = {x['key'] if 'key' in x else f"g{x['N']}_{x['m']}_{x['k']}_{x['r']}": x['q'] for x in json.load(open('/home/user/degree-diameter/research/squads/deep-49/r1/c2/candidates.json')) if x['keep']}
def table(m, k, r):
    N = m * k; rp = np.array([pow(r, j, m) for j in range(k)])
    a = np.arange(N) % m; j = np.arange(N) // m
    return ((a[:, None] + rp[j][:, None] * a[None, :]) % m + m * ((j[:, None] + j[None, :]) % k)).astype(np.int64)
def invariant(m, k, r):
    MT = table(m, k, r); N = MT.shape[0]; ar = np.arange(N)
    cur = ar.copy(); order = np.zeros(N, dtype=np.int64); done = np.zeros(N, bool); n = 1
    while True:
        hit = (cur == 0) & ~done
        order[hit] = n; done |= hit
        if done.all(): break
        cur = MT[cur, ar]; n += 1
    cen = int(np.all(MT == MT.T, axis=1).sum())
    cnt = sorted(collections.Counter(order.tolist()).items())
    return (N, cen, tuple(cnt))
classes = collections.defaultdict(list)
for m, k, r, N, key in rows:
    m, k, r, N = map(int, (m, k, r, N))
    classes[invariant(m, k, r) + (q_of[key],)].append((key, m, k, r))
multi = [v for v in classes.values() if len(v) > 1]
print('invariant classes', len(classes), 'multi-member classes', len(multi), 'members in multi', sum(len(v) for v in multi))
json.dump({'classes': [v for v in classes.values()]}, open('/home/user/degree-diameter/research/squads/deep-49/r1/c2/runs/classes.json', 'w'))
pairs = []
for v in multi:
    for key, m, k, r in v[1:]:
        pairs.append((v[0][0], v[0][1], v[0][2], v[0][3], key, m, k, r))
json.dump(pairs, open('/home/user/degree-diameter/research/squads/deep-49/r1/c2/runs/pairs.json', 'w'))
print('pairs to test', len(pairs))
