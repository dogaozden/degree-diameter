import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXG 1600
#define MAXN (2*MAXK*MAXG)
#define MAXE (MAXK*MAXG*MAXD)

static int dd, DD, kk, GG, MM, K2;
static int mulT[MAXG*MAXG];
static int invT[MAXG];
static int P[MAXD][MAXK], PI[MAXD][MAXK], S[MAXD][MAXK], SI[MAXD][MAXK];
static int vis[MAXN];
static int fr[MAXN], nx[MAXN];
static int vstamp = 0;
static uint64_t rs = 88172645463325252ULL;
static double tlimit;
static struct timespec t_start;
static int bestEu[MAXE], bestEv[MAXE];
static int bestN = 0, bestM = 0;

static uint64_t xr(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(xr() % (uint64_t)n); }
static double rnd01(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)(t.tv_sec - t_start.tv_sec) + 1e-9 * (double)(t.tv_nsec - t_start.tv_nsec);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Semidirect product Z_m x| Z_kk2, element (a,b) coded a*kk2+b,
   (a,b)(c,e) = (a + r^b c, b+e). */
static void build_group(int m, int kk2, int r) {
    MM = m; K2 = kk2; GG = m * kk2;
    int pw[MAXG];
    pw[0] = 1 % m;
    for (int b = 1; b < kk2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < GG; x++) {
        int a = x / kk2, b = x % kk2;
        for (int y = 0; y < GG; y++) {
            int c = y / kk2, e = y % kk2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            mulT[x * GG + y] = aa * kk2 + (b + e) % kk2;
        }
    }
    for (int x = 0; x < GG; x++)
        for (int y = 0; y < GG; y++)
            if (mulT[x * GG + y] == 0) { invT[x] = y; break; }
}

static int pick_group(int target) {
    for (int tries = 0; tries < 300 && target + tries <= MAXG; tries++) {
        int Gc = target + tries;
        int divs[64], nd = 0;
        for (int x = 1; x <= Gc && nd < 64; x++)
            if (Gc % x == 0) divs[nd++] = x;
        int k2 = divs[rndint(nd)];
        int m = Gc / k2;
        int r = 1;
        if (k2 > 1 && m >= 2) {
            int ok = 0;
            for (int t = 0; t < 100; t++) {
                int c = 1 + rndint(m - 1);
                if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; ok = 1; break; }
            }
            if (!ok) continue;
        }
        build_group(m, k2, r);
        return 1;
    }
    return 0;
}

static void init_layers(void) {
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < kk; i++) P[l][i] = i;
        for (int i = kk - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i]; P[l][i] = P[l][j]; P[l][j] = t;
        }
        for (int i = 0; i < kk; i++) PI[l][P[l][i]] = i;
        for (int i = 0; i < kk; i++) {
            S[l][i] = rndint(GG);
            SI[l][i] = invT[S[l][i]];
        }
    }
}

static void swap_P(int l, int i1, int i2) {
    int a = P[l][i1];
    P[l][i1] = P[l][i2];
    P[l][i2] = a;
    PI[l][P[l][i1]] = i1;
    PI[l][P[l][i2]] = i2;
}

/* Vertices: A_{i,g} = i*GG+g (i<kk), B_{j,h} = (kk+j)*GG+h.
   Layer l, index i: A_{i,g} ~ B_{P[l][i], g*S[l][i]}.
   Left multiplication is an automorphism, so BFS from the 2kk representatives
   suffices. Returns 0 iff the graph has diameter <= DD. */
static long cost_eval(void) {
    int N = 2 * kk * GG;
    int kG = kk * GG;
    long total = 0;
    for (int l1 = 0; l1 < dd; l1++)
        for (int l2 = l1 + 1; l2 < dd; l2++)
            for (int i = 0; i < kk; i++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) total += GG;
    for (int s = 0; s < 2 * kk; s++) {
        int src = s * GG;
        vstamp++;
        vis[src] = vstamp;
        int nf = 1, reached = 1;
        fr[0] = src;
        for (int dep = 0; dep < DD && nf > 0; dep++) {
            int nn = 0;
            for (int q = 0; q < nf; q++) {
                int u = fr[q];
                if (u < kG) {
                    int i = u / GG, g = u % GG;
                    for (int l = 0; l < dd; l++) {
                        int v = (kk + P[l][i]) * GG + mulT[g * GG + S[l][i]];
                        if (vis[v] != vstamp) { vis[v] = vstamp; nx[nn++] = v; }
                    }
                } else {
                    int idx = u - kG, j = idx / GG, h = idx % GG;
                    for (int l = 0; l < dd; l++) {
                        int i = PI[l][j];
                        int v = i * GG + mulT[h * GG + SI[l][i]];
                        if (vis[v] != vstamp) { vis[v] = vstamp; nx[nn++] = v; }
                    }
                }
            }
            reached += nn;
            memcpy(fr, nx, sizeof(int) * (size_t)nn);
            nf = nn;
        }
        total += N - reached;
    }
    return total;
}

static void save_graph(void) {
    int kG = kk * GG;
    int m = 0;
    for (int x = 0; x < kG; x++) {
        int i = x / GG, g = x % GG;
        int nb[MAXD];
        int c = 0;
        for (int l = 0; l < dd; l++) {
            int v = (kk + P[l][i]) * GG + mulT[g * GG + S[l][i]];
            int dup = 0;
            for (int q = 0; q < c; q++) if (nb[q] == v) { dup = 1; break; }
            if (!dup) nb[c++] = v;
        }
        for (int q = 0; q < c && m < MAXE; q++) {
            bestEu[m] = x;
            bestEv[m] = nb[q];
            m++;
        }
    }
    bestN = 2 * kG;
    bestM = m;
}

static int attempt(long iters) {
    init_layers();
    long cur = cost_eval();
    const double T0 = 5.0;
    for (long t = 0; t < iters && cur > 0; t++) {
        if ((t & 63) == 0 && elapsed() > tlimit) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        if (kk < 2 || rndint(2) == 0) {
            int l = rndint(dd), i = rndint(kk);
            int old = S[l][i], oldi = SI[l][i];
            int nv = rndint(GG);
            S[l][i] = nv;
            SI[l][i] = invT[nv];
            long c2 = cost_eval();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                S[l][i] = old;
                SI[l][i] = oldi;
            }
        } else {
            int l = rndint(dd), i1 = rndint(kk), i2 = rndint(kk);
            if (i1 == i2) continue;
            swap_P(l, i1, i2);
            long c2 = cost_eval();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                swap_P(l, i1, i2);
            }
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    tlimit = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 0;
    if (dd < 1 || dd > MAXD || DD < 2) { printf("0 0\n"); return 0; }
    clock_gettime(CLOCK_MONOTONIC, &t_start);

    int best_n = minN;
    static const int ks[5] = {1, 2, 2, 3, 4};
    while (elapsed() < tlimit) {
        kk = ks[rndint(5)];
        int base = best_n / (2 * kk);
        int target = base + 1 + rndint(base / 40 + 2);
        if (target > MAXG) continue;
        if (!pick_group(target)) continue;
        if (attempt(15000)) {
            int n = 2 * kk * GG;
            if (n > best_n) {
                best_n = n;
                save_graph();
            }
        }
    }
    if (bestN > minN) {
        printf("%d %d\n", bestN, bestM);
        for (int e = 0; e < bestM; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (exact families) and Python fallback search.
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


_PENALTY = 1000


def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs plus duplicate-dart penalties. Zero means valid."""
    seen = set()
    dup = 0
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            dup += 1
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen_v = [False] * N
        seen_v[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen_v[v]:
                        seen_v[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total + _PENALTY * dup


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_pm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _cost(k, G, D, darts, perms)
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    budget = max(2.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = t0 + budget

    # Bold path: C engine doing annealing over bi-Cayley lifts on semidirect
    # products Z_m x| Z_k2, climbing in order from the best graph so far.
    c_ok = False
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}", best_n],
                        timeout=budget + 4.0)
        n, e = lib.parse_graph_text(out)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
        c_ok = True
    except Exception:
        c_ok = False

    # Python fallback, used only if the C engine failed.
    if not c_ok:
        rng = random.Random(seed)
        while time.monotonic() < deadline:
            k = rng.choice([1, 2, 2, 3, 4])
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            order, mul = g
            res = _search(d, D, k, order, mul, rng, deadline, 500)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
