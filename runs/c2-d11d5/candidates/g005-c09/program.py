"""Bold revision: a C-side bi-Cayley voltage-lift annealer over semidirect groups Z_m x| Z_k2.

Instead of Python search plus a grow-by-two step, the C engine owns the whole search. It keeps a
band of candidate (k, group) pairs just above the best order found so far, anneals voltages and
block permutations for each candidate, and ratchets upward on success. Python only builds exact
starts (projective planes, Araujo-Pardo-Lopez, generalized quadrangles), calls the engine, and
checks every output with lib.is_valid. K_{d,d} is the fallback.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage:  prog d D seed time_limit [start_n]
 * stdin is ignored. stdout: "n m" + edges of the largest valid lift found, or "0 0".
 *
 * Model: group G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e)),
 * k A-blocks and k B-blocks of size G. Layer l maps A-block i to B-block sig[l][i] with
 * voltage sv[l][i]: A_{i,g} ~ B_{sig,g*s}. Each layer is a permutation, so the graph is
 * d-regular and bipartite. Left multiplication by G is an automorphism, so diameter <= D
 * holds iff every vertex is within distance D of all 2k block representatives.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDEG 32
#define MAXK 31
#define MAXN 65536
#define MAXK2 40
#define MAXCAND 6000
#define PATIENCE 4000
#define PEN 4

typedef struct { int k, m, k2, r, n; } Cand;

static int DEG, DIAM;
static int K, MM, K2, RR, G, N;
static int PW[MAXK2 + 1];

static int sig[MAXDEG][MAXK], sinv[MAXDEG][MAXK];
static int sv[MAXDEG][MAXK], svi[MAXDEG][MAXK];
static int nbr[MAXDEG][MAXN];
static int bestnbr[MAXDEG][MAXN];
static uint64_t s1[MAXN], s2[MAXN], bufX[MAXN], bufY[MAXN];
static uint64_t *ACC = bufX, *TMP = bufY;
static int have_best = 0, best_N = 0;
static Cand cand[MAXCAND];
static int ncand = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int aa = (int)(((long long)PW[b] * c + a) % MM);
    int bb = (b + e) % K2;
    return aa * K2 + bb;
}

static int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)PW[nb] * a) % MM;
    int aa = (int)((MM - t) % MM);
    return aa * K2 + nb;
}

static void setup_group(const Cand *c) {
    K = c->k;
    MM = c->m;
    K2 = c->k2;
    RR = c->r % c->m;
    G = MM * K2;
    N = 2 * K * G;
    PW[0] = 1 % MM;
    for (int b = 1; b < K2; b++) PW[b] = (int)((long long)PW[b - 1] * RR % MM);
}

static void refresh(int l, int i) {
    int j = sig[l][i];
    int s = sv[l][i], si = svi[l][i];
    int A = i * G, B = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][A + g] = B + gmul(g, s);
        nbr[l][B + g] = A + gmul(g, si);
    }
}

static void randomize(void) {
    for (int l = 0; l < DEG; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sig[l][i] = p[i];
            sinv[l][p[i]] = i;
            sv[l][i] = rndint(G);
            svi[l][i] = ginv(sv[l][i]);
        }
        for (int i = 0; i < K; i++) refresh(l, i);
    }
}

/* Returns unreached (vertex, representative) pairs + PEN * duplicate darts; writes reach masks to dst. */
static long evaluate(uint64_t *dst) {
    uint64_t *cur = s1, *nxt = s2;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[(long)b * G] |= 1ULL << b;
    for (int r = 0; r < DIAM; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < DEG; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += 2 * K - __builtin_popcountll(cur[v]);
    memcpy(dst, cur, sizeof(uint64_t) * (size_t)N);
    long dup = 0;
    for (int l = 0; l < DEG; l++)
        for (int l2 = l + 1; l2 < DEG; l2++)
            for (int i = 0; i < K; i++)
                if (sig[l][i] == sig[l2][i] && sv[l][i] == sv[l2][i]) dup++;
    return unreached + PEN * dup;
}

static void swap_sig(int l, int i1, int i2) {
    int t = sig[l][i1]; sig[l][i1] = sig[l][i2]; sig[l][i2] = t;
    sinv[l][sig[l][i1]] = i1;
    sinv[l][sig[l][i2]] = i2;
    refresh(l, i1);
    refresh(l, i2);
}

static void swapbuf(void) {
    uint64_t *t = ACC; ACC = TMP; TMP = t;
}

/* Anneal the current group until cost 0 (success) or the deadline. */
static int attempt(double deadline) {
    randomize();
    long cost = evaluate(TMP);
    swapbuf();
    long bestc = cost, since = 0;
    double T = 1.0;
    while (cost > 0) {
        if (now() > deadline) return 0;
        if (since > PATIENCE) {
            randomize();
            cost = evaluate(TMP);
            swapbuf();
            bestc = cost;
            since = 0;
            T = 1.0;
            continue;
        }
        double x = rnd01();
        if (K >= 2 && x < 0.2) {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            swap_sig(l, i1, i2);
            long c2 = evaluate(TMP);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                swapbuf();
            } else {
                swap_sig(l, i1, i2);
            }
        } else {
            int l = rndint(DEG), i = -1;
            if (rnd01() < 0.5) {
                int v = -1;
                for (int t = 0; t < 60 && v < 0; t++) {
                    int c = rndint(N);
                    if (__builtin_popcountll(ACC[c]) < 2 * K) v = c;
                }
                if (v >= 0) {
                    int blk = v / G;
                    i = blk < K ? blk : sinv[l][blk - K];
                }
            }
            if (i < 0) i = rndint(K);
            int old = sv[l][i];
            int ng = rndint(G);
            if (ng == old) { since++; continue; }
            sv[l][i] = ng;
            svi[l][i] = ginv(ng);
            refresh(l, i);
            long c2 = evaluate(TMP);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                swapbuf();
            } else {
                sv[l][i] = old;
                svi[l][i] = ginv(old);
                refresh(l, i);
            }
        }
        if (cost < bestc) { bestc = cost; since = 0; } else since++;
        T *= 0.9995;
        if (T < 0.15) T = 0.15;
    }
    return 1;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void add_cand(int k, int m, int k2, int r) {
    if (ncand >= MAXCAND) return;
    cand[ncand].k = k;
    cand[ncand].m = m;
    cand[ncand].k2 = k2;
    cand[ncand].r = r;
    cand[ncand].n = 2 * k * m * k2;
    ncand++;
}

/* Candidates (k, Z_m x| Z_k2) with order N = 2*k*m*k2 in (lo, hi]. */
static void gen_cands(int lo, int hi) {
    ncand = 0;
    for (int k = 1; k <= MAXK; k++) {
        int nmax = MAXN / (2 * k);
        int Gmin = lo / (2 * k) + 1;
        int Gmax = hi / (2 * k);
        if (Gmax > nmax) Gmax = nmax;
        for (int Gc = Gmin; Gc <= Gmax && ncand < MAXCAND; Gc++) {
            for (int k2 = 1; k2 <= Gc && k2 <= MAXK2; k2++) {
                if (Gc % k2) continue;
                int m = Gc / k2;
                if (m < 2) continue;
                if (k2 == 1) { add_cand(k, m, 1, 1); continue; }
                add_cand(k, m, k2, 1);
                for (int t = 0; t < 40; t++) {
                    int r = 1 + rndint(m - 1);
                    if (r == 1) continue;
                    if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) {
                        add_cand(k, m, k2, r);
                        break;
                    }
                }
            }
        }
    }
}

static void record_best(void) {
    have_best = 1;
    best_N = N;
    for (int l = 0; l < DEG; l++) memcpy(bestnbr[l], nbr[l], sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 2 || DEG > MAXDEG || DIAM < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    double t_end = t0 + limit * 0.95 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int width = 0, need_gen = 1;
    while (now() < t_end) {
        if (need_gen) {
            if (width <= 0) width = lo / 4 + 10;
            gen_cands(lo, lo + width);
            if (ncand == 0) {
                width *= 2;
                if (width > MAXN) break;
                continue;
            }
            need_gen = 0;
        }
        int idx = rndint(ncand);
        setup_group(&cand[idx]);
        double remaining = t_end - now();
        if (remaining <= 0.1) break;
        double slice = 0.15 * remaining;
        if (slice < 1.5) slice = 1.5;
        if (slice > remaining) slice = remaining;
        if (attempt(now() + slice)) {
            record_best();
            lo = N;
            width = 0;
            need_gen = 1;
        } else {
            cand[idx] = cand[--ncand];
            if (ncand == 0) {
                width *= 2;
                if (width > MAXN) break;
                need_gen = 1;
            }
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    long m = (long)best_N * DEG / 2;
    printf("%d %ld\n", best_N, m);
    for (int v = 0; v < best_N; v++)
        for (int l = 0; l < DEG; l++)
            if (v < bestnbr[l][v]) printf("%d %d\n", v, bestnbr[l][v]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact starts.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions. PG(2, q) has diameter 3, so it is valid for every D >= 3.
    pg_exact = False
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            pg_exact = (D == 3 and lib.is_prime_power(d - 1))
    except Exception:
        pass
    if pg_exact:
        return best

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: the C engine owns candidate generation, annealing and the ratchet.
    total = max(1.0, 0.85 * time_limit - 2.0)
    c_limit = max(1.0, total - 1.0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(c_limit, 2), best_n],
                         timeout=total + 2)
        n, e = lib.parse_graph_text(text)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
