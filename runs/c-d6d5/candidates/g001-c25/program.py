"""Group-voltage lifts searched by a C annealer, with a safe algebraic fallback.

Vertices of a lift are A_{i,g} = i*G + g and B_{j,h} = (kb+j)*G + h, where G is a
semidirect product Z_m x| Z_k. Layer l assigns A_i to B_{pi_l(i)} with voltage s, and
joins A_{i,g} to B_{j,g*s} for every g. Left multiplication by G is an automorphism, so
the diameter is at most D iff a BFS of depth D from each of the 2*kb base vertices
reaches everything. The C engine anneals over voltages and over within-layer target
swaps. Python picks group orders and factorizations and validates every result.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDARTS 512
#define MAXKB 8

static int dd, DD, kb, mm, kk, rr, G, NV;
static int *MT;
static int nd;
static int dI[MAXDARTS], dJ[MAXDARTS], dS[MAXDARTS];
static int bJ[MAXDARTS], bS[MAXDARTS];
static int *adj, *stampv, *cnt, *fr1, *fr2;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t next_rand(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rand_int(int n) { return (int)(next_rand() % (uint64_t)n); }

static double rand_unit(void) {
    return (double)(next_rand() >> 11) * (1.0 / 9007199254740992.0);
}

static void build_group(void) {
    int *pw = malloc(sizeof(int) * kk);
    pw[0] = 1 % mm;
    for (int b = 1; b < kk; b++) pw[b] = (pw[b - 1] * rr) % mm;
    G = mm * kk;
    MT = malloc(sizeof(int) * G * G);
    for (int x = 0; x < G; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < G; y++) {
            int c = y / kk, e = y % kk;
            int aa = (a + (pw[b] * c) % mm) % mm;
            int bb = (b + e) % kk;
            MT[x * G + y] = aa * kk + bb;
        }
    }
    free(pw);
}

static void build_adj(void) {
    for (int v = 0; v < NV; v++) cnt[v] = 0;
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t], s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (kb + j) * G + MT[g * G + s];
            if (cnt[a] < dd) adj[a * dd + cnt[a]] = b;
            cnt[a]++;
            if (cnt[b] < dd) adj[b * dd + cnt[b]] = a;
            cnt[b]++;
        }
    }
}

/* Number of (representative, vertex) pairs at distance > DD. Zero means valid. */
static long long cost_fn(void) {
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return 1000000000LL;
    build_adj();
    long long total = 0;
    int nreps = 2 * kb;
    for (int q = 0; q < nreps; q++) {
        int src = q * G;
        if (stamp >= 0x7ffffff0) {
            memset(stampv, 0, sizeof(int) * NV);
            stamp = 0;
        }
        stamp++;
        int *fr = fr1, *nx = fr2;
        int nf = 1;
        fr[0] = src;
        stampv[src] = stamp;
        int reached = 1;
        for (int lvl = 0; lvl < DD && nf > 0; lvl++) {
            int nn = 0;
            for (int x = 0; x < nf; x++) {
                int u = fr[x];
                for (int k = 0; k < dd; k++) {
                    int w = adj[u * dd + k];
                    if (stampv[w] != stamp) {
                        stampv[w] = stamp;
                        nx[nn++] = w;
                    }
                }
            }
            reached += nn;
            int *tmp = fr;
            fr = nx;
            nx = tmp;
            nf = nn;
        }
        total += NV - reached;
    }
    return total;
}

static void print_best(void) {
    memcpy(dJ, bJ, sizeof(int) * nd);
    memcpy(dS, bS, sizeof(int) * nd);
    printf("%d %d\n", NV, nd * G);
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t], s = dS[t];
        for (int g = 0; g < G; g++)
            printf("%d %d\n", i * G + g, (kb + j) * G + MT[g * G + s]);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: d D seed time m k r kb\n");
        return 1;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    mm = atoi(argv[5]);
    kk = atoi(argv[6]);
    rr = atoi(argv[7]);
    kb = atoi(argv[8]);
    if (dd < 1 || dd > 64 || DD < 1 || kb < 1 || kb > MAXKB || mm < 2 || kk < 1 || rr < 0) {
        printf("0 0\n");
        return 0;
    }
    nd = dd * kb;
    if (nd > MAXDARTS) {
        printf("0 0\n");
        return 0;
    }
    build_group();
    NV = 2 * kb * G;
    if (NV > 200000) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    adj = malloc(sizeof(int) * NV * dd);
    stampv = calloc(NV, sizeof(int));
    cnt = malloc(sizeof(int) * NV);
    fr1 = malloc(sizeof(int) * NV);
    fr2 = malloc(sizeof(int) * NV);

    /* Initial state: one random permutation per layer, random voltages. */
    int perm[MAXKB];
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rand_int(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < kb; i++) {
            dI[l * kb + i] = i;
            dJ[l * kb + i] = perm[i];
            dS[l * kb + i] = rand_int(G);
        }
    }

    long long cur = cost_fn();
    long long best = cur;
    memcpy(bJ, dJ, sizeof(int) * nd);
    memcpy(bS, dS, sizeof(int) * nd);

    clock_t c0 = clock();
    const double T0 = 3.0;
    long long it = 0;
    double frac = 0.0;
    while (best > 0) {
        if ((it & 63) == 0) {
            frac = (double)(clock() - c0) / CLOCKS_PER_SEC / tl;
            if (frac >= 1.0) break;
        }
        it++;
        double T = T0 * (1.0 - frac) + 0.05;
        int undoSwap = 0;
        int u1 = 0, u2 = 0, oldv = 0;
        if (kb >= 2 && rand_int(4) == 0) {
            int l = rand_int(dd);
            int i1 = rand_int(kb);
            int i2 = rand_int(kb - 1);
            if (i2 >= i1) i2++;
            u1 = l * kb + i1;
            u2 = l * kb + i2;
            int tmp = dJ[u1];
            dJ[u1] = dJ[u2];
            dJ[u2] = tmp;
            undoSwap = 1;
        } else {
            u1 = rand_int(nd);
            oldv = dS[u1];
            dS[u1] = rand_int(G);
        }
        long long c2 = cost_fn();
        int accept = (c2 <= cur);
        if (!accept) {
            double p = exp(-(double)(c2 - cur) / T);
            accept = (rand_unit() < p);
        }
        if (accept) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bJ, dJ, sizeof(int) * nd);
                memcpy(bS, dS, sizeof(int) * nd);
            }
        } else {
            if (undoSwap) {
                int tmp = dJ[u1];
                dJ[u1] = dJ[u2];
                dJ[u2] = tmp;
            } else {
                dS[u1] = oldv;
            }
        }
    }

    if (best == 0) print_best();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic fallbacks.
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
# Group selection and C search driver.
# ----------------------------------------------------------------------------

def _groups(G):
    """All semidirect factorizations (m, k, r) with m*k = G, m >= 2, r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _run_c_search(d, D, seed, secs, m, k, r, kb):
    """Run the C annealer for one group and base size. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{secs:.2f}", m, k, r, kb],
                        timeout=secs + 5.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if d <= 2 or best_n >= moore:
        return best

    rng = random.Random(seed)
    trial = 0
    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        secs = min(6.0, remaining - 0.5)
        kb = rng.choice([1, 1, 1, 2, 2, 3])
        G = best_n // (2 * kb) + 1 + rng.randrange(0, 10)
        groups = _groups(G)
        while not groups:
            G += 1
            groups = _groups(G)
        nonab = [g for g in groups if g[1] > 1 and g[2] != 1]
        if nonab and rng.random() < 0.7:
            m, k, r = rng.choice(nonab)
        else:
            m, k, r = rng.choice(groups)
        res = _run_c_search(d, D, seed * 7919 + trial, secs, m, k, r, kb)
        trial += 1
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best = res
            best_n = res[0]
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
