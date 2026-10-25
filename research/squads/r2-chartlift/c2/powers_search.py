"""Structured start for (k,q) = (5,3): charts with A_c = M^{e_c} (A_0 = I, e_0 = 0 WLOG), M a companion matrix over F_3,
b_c arbitrary nonzero.  Only the 4-walk singularity test is done here (closed forms below, checked against chartlib.py
by check_closed_form); pencils and diagonals are checked afterwards with chartflags.py.
Walk rules (chartlib.Chart.walk): a nonbacktracking 4-pattern (c1,c2,c3,c4) from side A is singular iff
  rank{A_c3 A_c2^-1 b_c1, A_c3 A_c2^-1 b_c2, b_c3, b_c4} < 4,
from side B iff rank{A_c2 A_c1^-1 b_c1, b_c2, b_c3, A_c3 A_c4^-1 b_c4} < 4.
With A_c = M^{e_c} every A-product is a power of M, so the cost depends only on the exponents e and vectors b.
usage: python3 powers_search.py SECONDS SEED OUTDIR"""
import sys, os, random, time, math
K, Q = 5, 3

def matvec(M, v): return tuple(sum(M[r][c] * v[c] for c in range(4)) % Q for r in range(4))
def matmul(X, Y): return tuple(tuple(sum(X[r][t] * Y[t][c] for t in range(4)) % Q for c in range(4)) for r in range(4))
ID = tuple(tuple(int(r == c) for c in range(4)) for r in range(4))

def companion(a):
    """matrix of x^4 + a3 x^3 + a2 x^2 + a1 x + a0 acting on column vectors (e_i -> e_{i+1})"""
    a0, a1, a2, a3 = a
    return ((0, 0, 0, (-a0) % Q), (1, 0, 0, (-a1) % Q), (0, 1, 0, (-a2) % Q), (0, 0, 1, (-a3) % Q))

def powers(M):
    P = [ID]; X = M
    while X != ID:
        P.append(X); X = matmul(X, M)
    return P                                  # P[t] = M^t, t = 0..N-1, N = order of M

def independent(vs):
    """True iff the four vectors are linearly independent over F_Q"""
    rows = [list(v) for v in vs]; r = 0
    for c in range(4):
        piv = next((i for i in range(r, 4) if rows[i][c] % Q), None)
        if piv is None: return False
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = 1 if rows[r][c] == 1 else 2
        rows[r] = [(x * inv) % Q for x in rows[r]]
        for i in range(4):
            if i != r and rows[i][c] % Q:
                f = rows[i][c]; rows[i] = [(rows[i][t] - f * rows[r][t]) % Q for t in range(4)]
        r += 1
    return True

def singular_count(e, b, P):
    N = len(P); cnt = 0
    for c2 in range(K):
        for c3 in range(K):
            if c3 == c2: continue
            T = P[(e[c3] - e[c2]) % N]
            Tb = [matvec(T, b[c]) for c in range(K)]
            for c1 in range(K):
                if c1 == c2: continue
                for c4 in range(K):
                    if c4 == c3: continue
                    if not independent([Tb[c1], Tb[c2], b[c3], b[c4]]): cnt += 1
    for c2 in range(K):
        for c3 in range(K):
            if c3 == c2: continue
            for c1 in range(K):
                if c1 == c2: continue
                v1 = matvec(P[(e[c2] - e[c1]) % N], b[c1])
                for c4 in range(K):
                    if c4 == c3: continue
                    v4 = matvec(P[(e[c3] - e[c4]) % N], b[c4])
                    if not independent([v1, b[c2], b[c3], v4]): cnt += 1
    return cnt

def chart_text(P, e, b):
    N = len(P); out = []
    for c in range(K):
        A = P[e[c] % N]; out.append(' '.join(str(A[r][s]) for r in range(4) for s in range(4)))
    for c in range(K): out.append(' '.join(map(str, b[c])))
    return '\n'.join(out) + '\n'

def random_point():
    while True:
        v = tuple(random.randrange(Q) for _ in range(4))
        if any(v): return v

POLYS = [(a0, a1, a2, a3) for a0 in (1, 2) for a1 in range(3) for a2 in range(3) for a3 in range(3)]

def search(seconds, seed, outdir):
    random.seed(seed); t0 = time.time(); gbest = None; restarts = 0; evals = 0
    while time.time() - t0 < seconds:
        restarts += 1
        a = random.choice(POLYS); M = companion(a); P = powers(M); N = len(P)
        e = [0] + [random.randrange(N) for _ in range(4)]
        b = [random_point() for _ in range(K)]
        cur = singular_count(e, b, P); evals += 1; stall = 0
        while stall < 300 and time.time() - t0 < seconds:
            e2, b2 = e[:], b[:]
            if random.random() < 0.5: e2[random.randrange(1, K)] = random.randrange(N)
            else: b2[random.randrange(K)] = random_point()
            new = singular_count(e2, b2, P); evals += 1
            if new <= cur or random.random() < math.exp(-(new - cur) / 0.7):
                stall = 0 if new < cur else stall + 1
                e, b, cur = e2, b2, new
            else: stall += 1
            if gbest is None or cur < gbest[0]:
                gbest = (cur, a, N, e[:], [tuple(x) for x in b], M)
                print('t=%.0fs best=%d poly=%s order=%d e=%s' % (time.time() - t0, cur, a, N, e), flush=True)
    cur, a, N, e, b, M = gbest
    P = powers(M)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, 'powers_best.txt'), 'w') as f: f.write(chart_text(P, e, b))
    print('FINAL best=%d poly=%s order=%d e=%s evals=%d restarts=%d' % (cur, a, N, e, evals, restarts), flush=True)

def check_closed_form(path, trials=3, seed=5):
    """compare singular_count with chartlib on random charts that have the powers structure"""
    sys.path.insert(0, '/home/user/degree-diameter/research/theorems/chartlift')
    from chartlib import Chart
    random.seed(seed)
    for _ in range(trials):
        a = random.choice(POLYS); M = companion(a); P = powers(M); N = len(P)
        e = [0] + [random.randrange(N) for _ in range(4)]; b = [random_point() for _ in range(K)]
        A = [P[e[c] % N] for c in range(K)]
        ch = Chart(3, [[list(r) for r in Mc] for Mc in A], [list(v) for v in b])
        print('closed form', singular_count(e, b, P), 'chartlib', len(ch.singular_patterns()))

if __name__ == '__main__':
    if sys.argv[1] == 'check':
        check_closed_form(None)
    else:
        search(float(sys.argv[1]), int(sys.argv[2]), sys.argv[3])
