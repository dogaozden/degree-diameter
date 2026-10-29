# Local search (tabu + SA-style acceptance) on dual segment sets: add a line, remove the lines needed to restore validity.
import sys, random, math, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c7')
from common import *
q = int(sys.argv[1]); start = sys.argv[2]; secs = float(sys.argv[3]); seed = int(sys.argv[4]); T0 = float(sys.argv[5]) if len(sys.argv) > 5 else 0.3
random.seed(seed)
q, N, LPa, PLa, X = load(f'{D}/data/hex_q{q}.bin')
LP = LPa.tolist(); PL = PLa.tolist()
inG = [False] * N
G = set(int(t) for t in open(start).read().split())
for L in G: inG[L] = True
cnt = [0] * N
for L in G:
    for p in LP[L]: cnt[p] += 1
def tc(L):  # number of points of L shared with another G-line
    return sum(1 for p in LP[L] if cnt[p] >= 2)
def add(L):
    inG[L] = True; G.add(L)
    for p in LP[L]: cnt[p] += 1
def rem(L):
    inG[L] = False; G.discard(L)
    for p in LP[L]: cnt[p] -= 1
def witnesses(L):  # G-lines (other than L) through the touched points of L
    W = set()
    for p in LP[L]:
        if cnt[p] >= 2:
            for K in PL[p]:
                if inG[K] and K != L: W.add(K)
    return W
def fix(M):
    """G currently contains M and maybe violations; remove lines until valid. returns removed list."""
    removed = []
    while True:
        # candidate violated lines: M and G-lines through points of M and of lines touched
        viol = None
        cand = {M}
        for p in LP[M]:
            for K in PL[p]:
                if inG[K]: cand.add(K)
        for L in list(cand):
            if inG[L] and tc(L) >= 2:
                viol = L; break
        if viol is None:
            # check neighbours of removed lines too: a removed line only lowers counts, so no new violations
            return removed
        L = viol
        opts = [L] + list(witnesses(L))
        R = random.choice(opts) if random.random() < 0.5 else L
        rem(R); removed.append(R)
        if R == M:
            return removed
def valid_now(): return all(tc(L) <= 1 for L in G)
best = len(G); bestG = set(G)
tabu = {}
it = 0; t_end = time.time() + secs; acc = 0
T = T0
while time.time() < t_end:
    it += 1
    # sample candidate lines not in G, pick the one with fewest covered-point conflicts
    bestc = None; bestcost = 10**9
    for _ in range(12):
        M = random.randrange(N)
        if inG[M] or tabu.get(M, -1) > it: continue
        cost = sum(cnt[p] for p in LP[M]) + random.random()*0.5
        if cost < bestcost: bestcost, bestc = cost, M
    if bestc is None: continue
    M = bestc
    add(M)
    removed = fix(M)
    if M in removed:
        # rejected outright
        pass
    delta = (1 if M not in removed else 0) - sum(1 for R in removed if R != M)
    if delta >= 0 or random.random() < math.exp(delta / T):
        acc += 1
        for R in removed:
            if R != M: tabu[R] = it + 7
        if delta > 0 or True:
            pass
        if len(G) > best:
            best = len(G); bestG = set(G)
            print(f'it {it} new best {best}', flush=True)
    else:
        # revert: remove M (if still in G), re-add removed lines
        if inG[M]: rem(M)
        for R in removed:
            if R != M: add(R)
    if it % 200000 == 0:
        print('it', it, 'cur', len(G), 'best', best, 'acc', acc, 'valid', valid_now(), flush=True)
assert valid_now()
out = f'/home/user/degree-diameter/research/squads/conics2-r1/c7/best_q{q}_seed{seed}.txt'
open(out, 'w').write(' '.join(map(str, sorted(bestG))))
print('done q', q, 'iters', it, 'best', best, 'file', out, 'valid(bestG)', valid(LPa, PLa, N, np.array(sorted(bestG))))
