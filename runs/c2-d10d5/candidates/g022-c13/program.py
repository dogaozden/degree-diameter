import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold construction: cyclic voltage lifts of a projective plane incidence graph.
#
# PG(2,q) has diameter 3, so a Z_m lift has slack to reach diameter D. The lift
# has n0*m vertices and keeps the base degree. Its validity depends only on
# whether every vertex reaches every base source (u,0) within D steps, because
# the Z_m action is an automorphism group. The C engine anneals the voltages
# with a transposed bitset: B[v] = set of base sources within distance t of v,
# which costs about n0/64 words per vertex.
#
# Safe fallbacks (K_{d,d}, PG(2,q), W(q)) are validated with lib.is_valid and
# returned whenever the lift search does not succeed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN0 8192
#define MAXE 200000
#define MAXDEG 64
#define MAXCAND 16

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}
static double clk_now(void) {
    return (double)clock() / CLOCKS_PER_SEC;
}

static int n0, E, DIAM;
static int ru[MAXE], rv[MAXE];
static int eu[MAXE], ev[MAXE];
static int side[MAXN0];
static int degu[MAXN0];
static int incE[MAXN0 * MAXDEG];
static int volt[MAXE];
static int solvolt[MAXE];
static int solM;
static int M, N, W;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int pc_vertex(const uint64_t *p) {
    int s = 0;
    for (int j = 0; j < W; j++) s += pc64(p[j]);
    return s;
}

static void init_B(uint64_t *B) {
    memset(B, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int u = 0; u < n0; u++) {
        size_t v = (size_t)u * M;
        B[v * W + (u >> 6)] |= 1ULL << (u & 63);
    }
}

/* dst[v] = src[v] OR (union of src[w] over neighbours w of v) */
static void step(const uint64_t *src, uint64_t *dst) {
    for (int u = 0; u < n0; u++) {
        int du = degu[u];
        const int *ie = incE + (size_t)u * MAXDEG;
        int sd = side[u];
        for (int g = 0; g < M; g++) {
            size_t v = (size_t)u * M + g;
            uint64_t *d = dst + v * W;
            const uint64_t *s0 = src + v * W;
            for (int j = 0; j < W; j++) d[j] = s0[j];
            for (int k = 0; k < du; k++) {
                int e = ie[k];
                int w, h;
                if (sd == 0) {
                    w = ev[e];
                    h = g + volt[e];
                    if (h >= M) h -= M;
                } else {
                    w = eu[e];
                    h = g - volt[e];
                    if (h < 0) h += M;
                }
                const uint64_t *s = src + ((size_t)w * M + h) * W;
                for (int j = 0; j < W; j++) d[j] |= s[j];
            }
        }
    }
}

static void eval_full(uint64_t *out, uint64_t *tmp) {
    uint64_t *a = out, *b = tmp;
    init_B(a);
    for (int t = 0; t < DIAM; t++) {
        step(a, b);
        uint64_t *x = a;
        a = b;
        b = x;
    }
    if (a != out) memcpy(out, a, sizeof(uint64_t) * (size_t)N * W);
}

static long long cost_of(const uint64_t *B) {
    long long c = 0;
    for (int v = 0; v < N; v++) {
        c += n0 - pc_vertex(B + (size_t)v * W);
    }
    return c;
}

static int anneal(int m, double slice) {
    if (m < 2) return 0;
    M = m;
    N = n0 * M;
    W = (n0 + 63) / 64;
    size_t sz = (size_t)N * W;
    uint64_t *P1 = malloc(sz * sizeof(uint64_t));
    uint64_t *P2 = malloc(sz * sizeof(uint64_t));
    uint64_t *P3 = malloc(sz * sizeof(uint64_t));
    if (!P1 || !P2 || !P3) {
        free(P1);
        free(P2);
        free(P3);
        return 0;
    }
    for (int e = 0; e < E; e++) volt[e] = rndint(M);
    uint64_t *cur = P1, *nw = P2, *tmp = P3;
    eval_full(cur, tmp);
    long long c = cost_of(cur);
    int ok = (c == 0);
    double t0 = clk_now();
    const double T0 = 6.0, T1 = 0.3;
    double T = T0;
    long long it = 0;
    while (!ok) {
        if ((it & 15) == 0) {
            double el = clk_now() - t0;
            if (el > slice) break;
            T = T0 * pow(T1 / T0, el / slice);
        }
        it++;
        int e = -1;
        if (rnd01() < 0.5) {
            int v = -1;
            for (int tr = 0; tr < 64; tr++) {
                int x = rndint(N);
                if (pc_vertex(cur + (size_t)x * W) < n0) {
                    v = x;
                    break;
                }
            }
            if (v >= 0) {
                int u = v / M;
                if (degu[u] > 0) e = incE[u * MAXDEG + rndint(degu[u])];
            }
        }
        if (e < 0) e = rndint(E);
        int old = volt[e];
        int nv = rndint(M - 1);
        if (nv >= old) nv++;
        volt[e] = nv;
        eval_full(nw, tmp);
        long long c2 = cost_of(nw);
        int acc = (c2 <= c) || (rnd01() < exp(-(double)(c2 - c) / T));
        if (acc) {
            uint64_t *s = cur;
            cur = nw;
            nw = s;
            c = c2;
            if (c == 0) ok = 1;
        } else {
            volt[e] = old;
        }
    }
    if (ok) {
        memcpy(solvolt, volt, sizeof(int) * (size_t)E);
        solM = M;
    }
    free(P1);
    free(P2);
    free(P3);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DIAM = atoi(argv[1]);
    double TL = atof(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    int nc = argc - 4;
    if (nc > MAXCAND) nc = MAXCAND;
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (scanf("%d %d", &n0, &E) != 2 || n0 < 1 || n0 > MAXN0 || E < 1 || E > MAXE) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < E; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (ru[i] < 0 || ru[i] >= n0 || rv[i] < 0 || rv[i] >= n0 || ru[i] == rv[i]) {
            printf("0 0\n");
            return 0;
        }
        if (degu[ru[i]] >= MAXDEG || degu[rv[i]] >= MAXDEG) {
            printf("0 0\n");
            return 0;
        }
        incE[(size_t)ru[i] * MAXDEG + degu[ru[i]]++] = i;
        incE[(size_t)rv[i] * MAXDEG + degu[rv[i]]++] = i;
    }

    /* 2-colour the base graph */
    for (int i = 0; i < n0; i++) side[i] = -1;
    int *qu = malloc(sizeof(int) * (size_t)n0);
    if (!qu) {
        printf("0 0\n");
        return 0;
    }
    for (int s = 0; s < n0; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail) {
            int u = qu[head++];
            for (int k = 0; k < degu[u]; k++) {
                int e = incE[(size_t)u * MAXDEG + k];
                int w = (ru[e] == u) ? rv[e] : ru[e];
                if (side[w] == -1) {
                    side[w] = 1 - side[u];
                    qu[tail++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    free(qu);
    for (int e = 0; e < E; e++) {
        if (side[ru[e]] == 0) {
            eu[e] = ru[e];
            ev[e] = rv[e];
        } else {
            eu[e] = rv[e];
            ev[e] = ru[e];
        }
    }

    double tstart = clk_now();
    int found = 0;
    for (int i = 0; i < nc; i++) {
        double rem = TL - (clk_now() - tstart);
        if (rem < 0.3) break;
        int m = atoi(argv[4 + i]);
        if (m < 2) continue;
        double slice = rem / (double)(nc - i);
        if (anneal(m, slice)) {
            found = 1;
            break;
        }
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }

    int NN = n0 * solM;
    printf("%d %lld\n", NN, (long long)E * solM);
    for (int e = 0; e < E; e++) {
        for (int g = 0; g < solM; g++) {
            int a = eu[e] * solM + g;
            int b = ev[e] * solM + (g + solvolt[e]) % solM;
            printf("%d %d\n", a, b);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions.
# ----------------------------------------------------------------------------

def _pg_base(d):
    """(q, incidence graph of PG(2,q)) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q, lib.projective_plane_incidence(q)
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
# Main build: exact constructions, then the C voltage-lift search, with
# every candidate passing lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
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

    if D == 2:
        return best

    base = _pg_base(d)
    if base is None:
        return best
    q, (pn, pe) = base
    consider(pn, pe)
    if D == 3:
        return best

    # W(q) with q = d-1 gives a diameter-4 base of order 2(q+1)(q^2+1).
    if D >= 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
        n_w = 2 * d * ((d - 1) ** 2 + 1)
        if n_w > best_n:
            try:
                wn, we = _gq_w(d - 1)
                consider(wn, we)
            except Exception:
                pass

    # Lift search: Z_m voltage lifts of PG(2,q), descending m, first success wins.
    end = t0 + min(0.8 * time_limit, time_limit - 8.0)
    n0 = pn
    goal = 4000 if (d, D) == (10, 5) else 2 * best_n
    hi = -(-goal // n0) + 1
    lo = max(2, best_n // n0 + 1)
    cands = list(range(hi, lo - 1, -1))[:7]
    left = end - time.monotonic()
    if cands and left > 5.0:
        c_tl = left - 1.5
        try:
            text = lib.run_c(C_SOURCE,
                             [D, round(c_tl, 2), int(seed) & 0x7FFFFFFF] + cands,
                             stdin_graph=(pn, pe),
                             timeout=left + 8.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
