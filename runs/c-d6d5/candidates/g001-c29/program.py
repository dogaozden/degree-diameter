import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over group voltages (semidirect products).
# Python handles constructions and validation. C does the heavy search.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXD 16
#define MAXG 2048
#define MAXN (2*MAXK*MAXG)
#define MAXE (MAXD*MAXK*MAXG)
#define BIG 1000000000LL

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n){ return (int)(rnd() % (uint64_t)n); }
static double rdbl(void){ return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_(int a, int b){ while (b){ int t = a % b; a = b; b = t; } return a; }
static int powmod(long long b, long long e, long long m){
    long long r = 1 % m; b %= m;
    while (e > 0){ if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return (int)r;
}

/* Group Z_M x| Z_K2 with element (a,b) coded a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int d_, D_, K, G, M, K2;
static int pw[16];
static int P[MAXD][MAXK];      /* layer permutations: dart (l,i) goes to B-vertex P[l][i] */
static int S[MAXD*MAXK];       /* voltage of dart t = l*K + i */
static int adj[MAXN*MAXD];
static int deg[MAXN];
static int stamp[MAXN];
static int curstamp = 0;
static int qbuf[MAXN];
static int outU[MAXE], outV[MAXE];
static int outN = 0, outM = 0;
static int haveOut = 0;
static int bestN = 0;

static inline int gmul(int x, int y){
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
}

static int sample_group(int g){
    static const int k2c[13] = {1,1,2,3,4,5,6,7,8,9,10,11,12};
    for (int tries = 0; tries < 80; tries++){
        int k2 = k2c[rint_(13)];
        if (g % k2) continue;
        int m = g / k2;
        if (m < 2) continue;
        int r = 1;
        if (k2 > 1){
            int found = 0;
            for (int t = 0; t < 60 && !found; t++){
                int cand = 1 + rint_(m - 1);
                if (gcd_(cand, m) == 1 && powmod(cand, k2, m) == 1 % m){ r = cand; found = 1; }
            }
            if (!found) continue;
        }
        G = g; K2 = k2; M = m;
        pw[0] = 1 % m;
        for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b-1] * r % m);
        return 1;
    }
    return 0;
}

static void build_adj(void){
    int N = 2 * K * G;
    memset(deg, 0, sizeof(int) * N);
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++){
            int t = l * K + i, j = P[l][i], s = S[t];
            for (int g = 0; g < G; g++){
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * d_ + deg[a]++] = b;
                adj[b * d_ + deg[b]++] = a;
            }
        }
}

/* Number of (representative, vertex) pairs at distance > D_. Zero means valid. */
static long long cost_fn(void){
    int T = d_ * K;
    for (int x = 0; x < T; x++)
        for (int y = x + 1; y < T; y++){
            int ix = x % K, iy = y % K;
            int jx = P[x / K][ix], jy = P[y / K][iy];
            if (ix == iy && jx == jy && S[x] == S[y]) return BIG;
        }
    build_adj();
    int N = 2 * K * G;
    long long total = 0;
    int reps[2 * MAXK];
    int nr = 0;
    for (int i = 0; i < K; i++) reps[nr++] = i * G;
    for (int j = 0; j < K; j++) reps[nr++] = (K + j) * G;
    for (int r = 0; r < nr; r++){
        curstamp++;
        int src = reps[r];
        int tail = 1, ls = 0, le = 1;
        qbuf[0] = src;
        stamp[src] = curstamp;
        for (int dep = 0; dep < D_; dep++){
            if (ls == le) break;
            for (int x = ls; x < le; x++){
                int u = qbuf[x];
                for (int e = 0; e < d_; e++){
                    int v = adj[u * d_ + e];
                    if (stamp[v] != curstamp){ stamp[v] = curstamp; qbuf[tail++] = v; }
                }
            }
            ls = le; le = tail;
        }
        total += N - tail;
    }
    return total;
}

static long long anneal(int iters, double T0){
    for (int l = 0; l < d_; l++){
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--){
            int j = rint_(i + 1);
            int tmp = P[l][i]; P[l][i] = P[l][j]; P[l][j] = tmp;
        }
    }
    for (int t = 0; t < d_ * K; t++) S[t] = rint_(G);

    long long cost = cost_fn();
    long long best = cost;
    for (int it = 0; it < iters && best > 0; it++){
        double T = T0 * (1.0 - (double)it / iters) + 0.05;
        int type, l = 0, a1 = 0, a2 = 0, oldS = 0;
        if (K > 1 && rint_(2) == 0){
            type = 1;
            l = rint_(d_);
            a1 = rint_(K);
            a2 = rint_(K - 1);
            if (a2 >= a1) a2++;
            int tmp = P[l][a1]; P[l][a1] = P[l][a2]; P[l][a2] = tmp;
        } else {
            type = 2;
            a1 = rint_(d_ * K);
            oldS = S[a1];
            S[a1] = rint_(G);
        }
        long long c2 = cost_fn();
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)){
            cost = c2;
            if (cost < best) best = cost;
        } else {
            if (type == 1){
                int tmp = P[l][a1]; P[l][a1] = P[l][a2]; P[l][a2] = tmp;
            } else {
                S[a1] = oldS;
            }
        }
    }
    return best;
}

static void emit(void){
    int m = 0;
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++){
            int t = l * K + i, j = P[l][i], s = S[t];
            for (int g = 0; g < G; g++){
                outU[m] = i * G + g;
                outV[m] = (K + j) * G + gmul(g, s);
                m++;
            }
        }
    outM = m;
    outN = 2 * K * G;
    bestN = outN;
    haveOut = 1;
}

int main(int argc, char **argv){
    if (argc < 6){ printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    double budget = atof(argv[4]);
    bestN = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 2){ printf("0 0\n"); return 0; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd();

    static const int ks[6] = {1, 1, 1, 2, 2, 3};
    clock_t c0 = clock();
    while ((double)(clock() - c0) / CLOCKS_PER_SEC < budget){
        K = ks[rint_(6)];
        int base = bestN / (2 * K);
        int spread = base / 6 + 1;
        if (spread < 3) spread = 3;
        int g = base + 1 + rint_(spread);
        if (g < 2) g = 2;
        if (g > MAXG) continue;
        if (!sample_group(g)) continue;
        long long c = anneal(3000, 3.0);
        if (c == 0){
            int n = 2 * K * G;
            if (n > bestN) emit();
        }
    }
    if (haveOut){
        printf("%d %d\n", outN, outM);
        for (int m = 0; m < outM; m++) printf("%d %d\n", outU[m], outV[m]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


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
# Python fallback search (used only if the C engine fails to run).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a group of order G. Returns (n, edges) or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        return _edges(k, G, best_darts, best_perms)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: the C engine anneals group-voltage lifts for most of the budget.
    c_ok = False
    if d >= 3 and D >= 2:
        c_budget = 0.75 * time_limit - (time.monotonic() - start) - 1.0
        if c_budget >= 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                 timeout=c_budget + 8.0)
                n, e = lib.parse_graph_text(text)
                if n > 0 and e:
                    consider(n, e)
                c_ok = True
            except (RuntimeError, ValueError):
                c_ok = False

    # Python fallback, used when the C engine is unavailable, or with leftover time.
    if not c_ok:
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 1, 2, 2, 3])
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
            res = _search(d, D, k, G, rng, 1500, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
