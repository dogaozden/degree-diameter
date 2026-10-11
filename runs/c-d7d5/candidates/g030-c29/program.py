import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (kept as safe starting points).
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
# New construction family: bi-Cayley lifts over semidirect products
# Z_m x|_r Z_k with a base of K vertices per side, searched by SIMULATED
# ANNEALING (Metropolis acceptance, geometric cooling, reheating per attempt)
# on the number of unreached pairs. This replaces the earlier breakout /
# clause-weighting search with a different acceptance and move scheme.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Each P[l] is a permutation, so the graph
# is bipartite and d-regular. Cost = unreached pairs from the 2K base
# representatives + PEN * duplicate darts. Cost 0 means a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 3
#define MAXD 64
#define MAXN 20000
#define MAXC 4000
#define PEN 20
#define ITERS 15000

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3, K = 1;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int bestP[MAXD][MAXK], bestS[MAXD][MAXK];
static int adj[MAXN * MAXD];
static int cnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stamp_ = 0;
static double deadline = 0.0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)(t * GK + (b + d) % GK);
}

static long long evaluate(void) {
    int N = 2 * K * GG;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                int a = i * GG + g;
                int b = (K + j) * GG + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * GG;
        stamp_++;
        int head = 0, tail = 0;
        vis[src] = stamp_;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp_) {
                        vis[v] = stamp_;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return raw + (long long)PEN * dup;
}

static void random_init(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(GG);
    }
}

/* Simulated annealing from a random start. Returns 1 if a valid state
   (cost 0) was found; P and S are left at the best state seen. */
static int anneal(long iters) {
    random_init();
    long long cur = evaluate();
    long long best = cur;
    memcpy(bestP, P, sizeof P);
    memcpy(bestS, S, sizeof S);
    const double T0 = 4.0, T1 = 0.3;
    for (long it = 0; it < iters && best > 0; it++) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rint_(Dd), i = rint_(K);
        int swapped = 0, i2 = 0, olds = 0;
        if (K >= 2 && rint_(3) == 0) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int t = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = t;
            swapped = 1;
        } else {
            olds = S[l][i];
            S[l][i] = rint_(GG);
        }
        long long c2 = evaluate();
        long long delta = c2 - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bestP, P, sizeof P);
                memcpy(bestS, S, sizeof S);
            }
        } else {
            if (swapped) {
                int t = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = t;
            } else {
                S[l][i] = olds;
            }
        }
    }
    memcpy(P, bestP, sizeof P);
    memcpy(S, bestS, sizeof S);
    evaluate();
    return best == 0;
}

#define MAXCAND MAXC

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    Dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long long best_n = atoll(argv[5]);
    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }

    static int cK[MAXCAND], cm[MAXCAND], ck[MAXCAND], cr[MAXCAND];
    static int elig[MAXCAND];
    int nc = 0;
    for (int a = 6; a < argc && nc < MAXCAND; a++) {
        int kk = 0, m = 0, k = 0, r = 0;
        if (sscanf(argv[a], "%d,%d,%d,%d", &kk, &m, &k, &r) == 4 &&
            kk >= 1 && kk <= MAXK && m >= 1 && k >= 1 && k <= 60 && r >= 1 &&
            2LL * kk * m * k <= MAXN) {
            cK[nc] = kk;
            cm[nc] = m;
            ck[nc] = k;
            cr[nc] = r;
            nc++;
        }
    }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;

    int have = 0;
    int sK = 1, sm = 1, sk = 1, sr = 1;
    static int sP[MAXD][MAXK], sS[MAXD][MAXK];

    while (now_s() < deadline) {
        int ne = 0;
        for (int c = 0; c < nc; c++) {
            long long N = 2LL * cK[c] * cm[c] * ck[c];
            if (N > best_n) elig[ne++] = c;
        }
        if (ne == 0) break;
        int pick = elig[rint_(ne)];
        K = cK[pick];
        set_group(cm[pick], ck[pick], cr[pick]);
        int ok = anneal(ITERS);
        if (ok) {
            best_n = 2LL * K * GG;
            have = 1;
            sK = K;
            sm = cm[pick];
            sk = ck[pick];
            sr = cr[pick];
            memcpy(sP, P, sizeof P);
            memcpy(sS, S, sizeof S);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    K = sK;
    set_group(sm, sk, sr);
    memcpy(P, sP, sizeof P);
    memcpy(S, sS, sizeof S);
    int N = 2 * K * GG;
    long m = (long)Dd * K * GG;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < GG; g++) {
                printf("%d %d\n", i * GG + g, (K + j) * GG + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


_KF = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 24, 27, 28, 30, 36)


def _candidates(d, D, best_n, seed, cap=800):
    """Candidate groups (K, m, k, r) meaning K base vertices per side and group Z_m x|_r Z_k.

    Orders are targeted at a window of the Moore bound that contains the known
    record scale; the C side only uses entries whose order beats best_n.
    """
    moore = lib.moore_bound(d, D)
    rng = random.Random(seed)
    out = []
    for K in (1, 2, 3):
        lo = max(best_n // (2 * K) + 1, int(0.22 * moore) // (2 * K) + 1)
        hi = max(int(0.42 * moore) // (2 * K), lo + 20)
        hi = min(hi, 3000)
        for G in range(lo, hi + 1):
            if G > 3000:
                break
            for k in _KF:
                if G % k:
                    continue
                m = G // k
                if m < 2:
                    continue
                if k == 1:
                    out.append((K, m, 1, 1))
                    continue
                out.append((K, m, k, 1))  # direct product Z_m x Z_k
                found = 0
                for r in range(2, min(m, 150)):
                    if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                        out.append((K, m, k, r))
                        found += 1
                        if found >= 2:
                            break
        if len(out) > 6 * cap:
            break
    rng.shuffle(out)
    return [f"{K},{m},{k},{r}" for (K, m, k, r) in out[:cap]]


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealed bi-Cayley lifts over semidirect products, seeded with best_n.
    if d >= 3 and D >= 3 and d <= 64:
        c_budget = min(0.8 * time_limit, time_limit - 12.0)
        if c_budget >= 2.0:
            try:
                cands = _candidates(d, D, best_n, seed)
                if cands:
                    args = [d, D, seed, f"{c_budget:.2f}", best_n] + cands
                    out = lib.run_c(C_SOURCE, args, timeout=time_limit - 4.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
