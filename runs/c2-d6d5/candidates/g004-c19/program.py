import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 6
#define GMAX 800
#define MAXGR 512

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0, haveBest = 0;
static int trials[MAXK + 1], wins[MAXK + 1];

/* Group library received from Python: each group is a full multiplication table
   with identity at index 0; MT[g*G+s] = g*s, RS[s*G+h] = g with g*s = h. */
static int ngr = 0;
static int grG[MAXGR];
static int *grM[MAXGR], *grR[MAXGR];

static void parse_groups(const int *P, int L) {
    if (L < 1) return;
    int pos = 0;
    int cnt = P[pos++];
    for (int t = 0; t < cnt && ngr < MAXGR; t++) {
        if (pos >= L) break;
        int G = P[pos++];
        if (G < 2 || G > GMAX) break;
        if (pos + G * G > L) break;
        const int *T = P + pos;
        pos += G * G;
        int ok = 1;
        for (int x = 0; x < G && ok; x++)
            if (T[x] != x || T[x * G] != x) ok = 0;
        int *seen = malloc(sizeof(int) * (size_t)G);
        for (int s = 0; s < G && ok; s++) {
            for (int g = 0; g < G; g++) seen[g] = 0;
            for (int g = 0; g < G; g++) {
                int h = T[g * G + s];
                if (h < 0 || h >= G || seen[h]) { ok = 0; break; }
                seen[h] = 1;
            }
        }
        free(seen);
        if (!ok) continue;
        int *M = malloc(sizeof(int) * (size_t)G * G);
        int *R = malloc(sizeof(int) * (size_t)G * G);
        memcpy(M, T, sizeof(int) * (size_t)G * G);
        for (int g = 0; g < G; g++)
            for (int s = 0; s < G; s++)
                R[s * G + M[g * G + s]] = g;
        grG[ngr] = G; grM[ngr] = M; grR[ngr] = R; ngr++;
    }
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

/* Cost = unreached (base, vertex) pairs + 1000 * duplicate darts.
   Left translation by the group is an automorphism, so only the 2k block
   base vertices need to reach everything. */
static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static int search(double tend, int iters, int patience) {
    int k = K_, d = d_, G = G_;
    u64 full = (1ULL << (2 * k)) - 1;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            setdart(l, i, lay[l][i], VS[l][i]);
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    int last = 0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if (t - last > patience) break;
        if ((t & 63) == 0 && now() > tend) break;
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.4) temp = 0.4;
        if (k >= 2 && rndu() < 0.25) {
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            setdart(l, i1, t2, VS[l][i1]);
            setdart(l, i2, t1, VS[l][i2]);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                setdart(l, i1, t1, VS[l][i1]);
                setdart(l, i2, t2, VS[l][i2]);
            }
        } else {
            int l = rndi(d), i = rndi(k);
            if (rndu() < 0.4) {
                int v = -1;
                for (int tr = 0; tr < 8; tr++) {
                    int c = rndi(2 * k * G);
                    if (rch[c] != full) { v = c; break; }
                }
                if (v >= 0) {
                    int blk = v / G;
                    if (blk < k) i = blk;
                    else {
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == blk - k) { i = ii; break; }
                    }
                }
            }
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            setdart(l, i, lay[l][i], nw);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                VS[l][i] = old;
                setdart(l, i, lay[l][i], old);
            }
        }
    }
    return cost == 0;
}

static int pick_k(void) {
    if (rndu() < 0.2) return 1 + rndi(MAXK);
    double bs = -1.0;
    int bk = 1;
    for (int k = 1; k <= MAXK; k++) {
        double s = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rndu();
        if (s > bs) { bs = s; bk = k; }
    }
    return bk;
}

/* Groups g with 2*k*|G| > bestN (so a success would improve the best). */
static int feas(int k, int *fe) {
    int n = 0;
    for (int gi = 0; gi < ngr; gi++)
        if (2 * k * grG[gi] > bestN) fe[n++] = gi;
    return n;
}

static void store_best(void) {
    int kG = K_ * G_;
    int cnt = kG * d_;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
    int p = 0;
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < d_; l++) {
            ne[2 * p] = u;
            ne[2 * p + 1] = nb[l * N_ + u];
            p++;
        }
    free(bE);
    bE = ne;
    bEc = cnt;
    bestN = N_;
    haveBest = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    double tend = now() + atof(argv[4]);
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    int minN = (argc > 5) ? atoi(argv[5]) : 2;
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Input: "n m" header followed by 2m integers carrying the group payload. */
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) m0 = 0;
    if (m0 < 0) m0 = 0;
    int L = 2 * m0;
    int *P = malloc(sizeof(int) * (size_t)(L + 1));
    int Lr = 0;
    for (int i = 0; i < L; i++) {
        if (scanf("%d", &P[i]) != 1) break;
        Lr++;
    }
    parse_groups(P, Lr);
    free(P);
    (void)n0;
    if (ngr == 0) { printf("0 0\n"); return 0; }

    bestN = minN - 1;
    int iters = 40000, patience = 6000;
    static int fe[MAXGR];

    while (now() < tend) {
        int k = pick_k();
        int nf = feas(k, fe);
        if (nf == 0) {
            int got = 0;
            for (int kk = 1; kk <= MAXK; kk++) {
                nf = feas(kk, fe);
                if (nf > 0) { k = kk; got = 1; break; }
            }
            if (!got) break;
        }
        int gi = fe[rndi(nf)];
        MT = grM[gi];
        RS = grR[gi];
        G_ = grG[gi];
        K_ = k;
        alloc_state(2 * k * G_);
        trials[k]++;
        if (search(tend, iters, patience)) {
            wins[k]++;
            if (N_ > bestN) store_best();
        }
    }

    if (!haveBest) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
    return 0;
}
'''


MAXK = 6
GMAX = 800
TABLE_BUDGET = 3_000_000
WINDOW = 8


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Groups: multiplication tables with identity at index 0.
# ----------------------------------------------------------------------------

def _is_prime(q):
    if q < 2:
        return False
    return all(q % p for p in range(2, int(q ** 0.5) + 1))


def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _metacyclic(m, k2, r):
    """Z_m x|_r Z_k2 with (a,b)(c,e) = (a + r^b c, b + e), element (a,b) coded a*k2+b."""
    G = m * k2
    pw = [pow(r, t, m) for t in range(k2)]
    A = [x // k2 for x in range(G)]
    B = [x % k2 for x in range(G)]
    M = [0] * (G * G)
    for x in range(G):
        a, b = A[x], B[x]
        pb = pw[b]
        base = x * G
        for y in range(G):
            c, e = A[y], B[y]
            M[base + y] = ((a + pb * c) % m) * k2 + (b + e) % k2
    return G, M


def _p3(p, twist):
    """Order p^3 group: Heisenberg (twist=True) or elementary abelian (twist=False)."""
    G = p ** 3
    trip = [(x // (p * p), (x // p) % p, x % p) for x in range(G)]
    M = [0] * (G * G)
    for x in range(G):
        a, b, c = trip[x]
        base = x * G
        for y in range(G):
            a2, b2, c2 = trip[y]
            cc = c + c2 + (a * b2 if twist else 0)
            M[base + y] = (((a + a2) % p) * p + (b + b2) % p) * p + cc % p
    return G, M


def _specs_for_order(G):
    """Group descriptions of order G that the pool knows how to build."""
    out = []
    for k2 in _divisors(G):
        m = G // k2
        if m < 2:
            continue
        units = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not units:
            continue
        step = max(1, len(units) // 3)
        for r in units[::step][:4]:   # units[0] == 1 (the direct product)
            out.append(('meta', m, k2, r))
    p = round(G ** (1.0 / 3.0))
    for q in (p - 1, p, p + 1):
        if q >= 2 and q ** 3 == G and _is_prime(q):
            out.append(('heis', q))
            out.append(('ab3', q))
    return out


def _group_pool(best_n, target_n):
    """Groups (order, table) for bi-Cayley lifts with k base pairs and 2kG > best_n.

    Orders are taken near the target order (roughly the record scale, aiming to beat
    it) and near the current best. Nonabelian groups are included on purpose.
    """
    cand = {}
    for k in range(1, MAXK + 1):
        centres = [(target_n // (2 * k), 0), (best_n // (2 * k) + 1, 1)]
        for c, pri in centres:
            for G in range(max(2, c - WINDOW), min(GMAX, c + WINDOW) + 1):
                if 2 * k * G <= best_n:
                    continue
                for spec in _specs_for_order(G):
                    key = (G,) + spec
                    rank = (k, pri)
                    if key not in cand or rank < cand[key]:
                        cand[key] = rank
    rng = random.Random(12345 + best_n)
    keys = sorted(cand, key=lambda kk: (cand[kk], rng.random()))

    groups = []
    used = 0
    for key in keys:
        G = key[0]
        if used + G * G > TABLE_BUDGET:
            continue
        spec = key[1:]
        if spec[0] == 'meta':
            Gm, M = _metacyclic(spec[1], spec[2], spec[3])
        elif spec[0] == 'heis':
            Gm, M = _p3(spec[1], True)
        else:
            Gm, M = _p3(spec[1], False)
        if Gm != G:
            continue
        groups.append((Gm, M))
        used += G * G
    return groups


def _payload(groups):
    """Pack the group tables as graph-text integers: header "0 m", then m edge lines of 2 ints."""
    P = [len(groups)]
    for G, M in groups:
        P.append(G)
        P.extend(M)
    if len(P) % 2:
        P.append(0)
    edges = [(P[i], P[i + 1]) for i in range(0, len(P), 2)]
    return (0, edges)


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Main build: exact constructions first, then the C bi-Cayley search over a
# pool of diverse (including nonabelian) groups, then slack extension.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    budget = max(1.0, min(0.7 * time_limit, time_limit - 14.0))
    try:
        target_n = max(best_n + 1, int(0.44 * lib.moore_bound(d, D)))
        groups = _group_pool(best_n, target_n)
        if groups:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                            stdin_graph=_payload(groups), timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
    except Exception:
        pass

    # Use any spare degree in the best graph to add vertices (cheap, time-bounded).
    rng = random.Random(seed)
    try:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, start + time_limit - 5.0)
        consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
