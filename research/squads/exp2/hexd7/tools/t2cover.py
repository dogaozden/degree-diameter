"""Can the 3-balls of q(q+1) lines cover Opp(p)? (type-2 routes only). Local search on max coverage.
usage: python3 t2cover.py HEXBIN nsets seconds seed"""
import sys, struct, random, time
from collections import deque
fn, nsets, secs, seed = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
random.seed(seed)
with open(fn, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12)); Q1 = q + 1
    LP = struct.unpack(f'{L*Q1}i', f.read(4 * L * Q1))
lp = [LP[l*Q1:(l+1)*Q1] for l in range(L)]
pl = [[] for _ in range(N)]
for l in range(L):
    for x in lp[l]: pl[x].append(l)
def bfs(src_is_line, s):
    d = [255] * (2 * N); st = (N + s) if src_is_line else s; d[st] = 0; dq = deque([st])
    while dq:
        v = dq.popleft()
        nb = [N + l for l in pl[v]] if v < N else lp[v - N]
        for w in nb:
            if d[w] == 255: d[w] = d[v] + 1; dq.append(w)
    return d
p = random.randrange(N); d = bfs(False, p)
opp = [x for x in range(N) if d[x] == 6]; idx = {x: i for i, x in enumerate(opp)}
cand = [l for l in range(L) if d[N + l] == 5]
def ball3(l):
    s = set()
    for y in lp[l]:
        s.add(y)
        for l2 in pl[y]:
            if l2 == l: continue
            for x in lp[l2]: s.add(x)
    return s
B = {}
for l in cand:
    m = 0
    for x in ball3(l):
        if x in idx: m |= 1 << idx[x]
    B[l] = m
full = (1 << len(opp)) - 1
print(f"q={q} |Opp(p)|={len(opp)} candidate lines={len(cand)} set size={bin(B[cand[0]]).count('1')} need >= {len(opp)//bin(B[cand[0]]).count('1')}")
# greedy
cur = []; cov = 0
for _ in range(nsets):
    best = max(cand, key=lambda l: bin(B[l] & ~cov).count('1'))
    cur.append(best); cov |= B[best]
print("greedy coverage", bin(cov).count('1'))
# local search: replace one set, accept if coverage does not drop (count multiplicities)
from collections import Counter
t0 = time.time(); bestc = bin(cov).count('1')
def coverage(sets):
    c = 0
    for l in sets: c |= B[l]
    return bin(c).count('1')
it = 0
while time.time() - t0 < secs and bestc < len(opp):
    it += 1
    i = random.randrange(nsets)
    rest = 0
    for j, l in enumerate(cur):
        if j != i: rest |= B[l]
    unc = full & ~rest
    # candidate: a line covering a random uncovered point
    ul = [k for k in range(len(opp)) if unc >> k & 1]
    x = opp[random.choice(ul)]
    # lines within distance 3 of x that are candidates
    cs = set()
    for l1 in pl[x]:
        cs.add(l1)
        for y in lp[l1]:
            if y == x: continue
            for l2 in pl[y]: cs.add(l2)
    cs = [l for l in cs if l in B]
    nl = max(cs, key=lambda l: bin(B[l] & unc).count('1'))
    newc = bin(rest | B[nl]).count('1')
    if newc >= bin(rest | B[cur[i]]).count('1'):
        cur[i] = nl
        if newc > bestc: bestc = newc; print(f"  it {it} coverage {bestc} ({time.time()-t0:.0f}s)", flush=True)
print("best coverage", bestc, "of", len(opp), "with", nsets, "sets")
