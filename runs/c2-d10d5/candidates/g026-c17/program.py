import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction for large (d, D): random bipartite d-regular graphs repaired
# by edge switches.
#
# The C engine works on a fixed number of vertices per side, h. A graph is a
# union of d random perfect matchings between the two sides, with duplicate
# edges removed by local swaps. Cost = number of unordered vertex pairs at
# distance > D (computed exactly with bitset BFS). Simulated annealing on
# 2-switches (which keep the graph d-regular and bipartite) drives the cost
# to zero. Defect-targeted switches are used with probability 0.6.
#
# Growth: the engine searches for the largest h that it can repair. It starts
# from a comfortable size, grows by an adaptive step (up/down on success and
# failure), and keeps the best valid graph. The output is always the last
# state that reached cost 0, which the engine checks itself. Python re-checks
# every candidate with lib.is_valid and keeps the K_{d,d} fallback otherwise.
# Exact PG(2,q) and W(q) constructions remain as start candidates and early
# returns for the calibration cases.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define HMAX_CAP 6000
#define EVALS 500

static int DEG, D_, H, N2, W, HMAXV;
static int *adj, *adjbest, *P;
static uint64_t *RB[3];
static int *BD[3];
static int ci, ca, cs;
static int bestH;
static double TL, tstart;
static int timed_out;
static uint64_t rs;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static double elapsed(void) {
    return now_s() - tstart;
}

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

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_nb(int v, int w) {
    const int *row = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++)
        if (row[k] == w) return 1;
    return 0;
}

static void repl(int v, int oldw, int neww) {
    int *row = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++) {
        if (row[k] == oldw) {
            row[k] = neww;
            return;
        }
    }
}

/* Edges (a1,b1),(a2,b2) become (a1,b2),(a2,b1). Applying sw(a1,b2,a2,b1) reverts it. */
static void sw(int a1, int b1, int a2, int b2) {
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
}

/* Unreached unordered pairs; fills bad[v] = unreached count of v. Result in out. */
static int64_t eval_buf(uint64_t *out, uint64_t *scr, int *bad) {
    const int n = N2, w = W;
    const size_t total = (size_t)n * (size_t)w;
    memset(out, 0, sizeof(uint64_t) * total);
    for (int v = 0; v < n; v++)
        out[(size_t)v * w + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    uint64_t *p = out, *q = scr;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = q + (size_t)v * w;
            const uint64_t *src = p + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            const int *nb = adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *s2 = p + (size_t)nb[k] * w;
                for (int x = 0; x < w; x++) dst[x] |= s2[x];
            }
        }
        uint64_t *tmp = p;
        p = q;
        q = tmp;
    }
    if (p != out) memcpy(out, p, sizeof(uint64_t) * total);
    int64_t sum = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *r = out + (size_t)v * w;
        for (int x = 0; x < w; x++) c += pc64(r[x]);
        bad[v] = n - c;
        sum += bad[v];
    }
    return sum / 2;
}

/* True if putting B-index pv into row i for layer l would duplicate an edge. */
static int conflict(int i, int l, int pv) {
    int b = H + pv;
    const int *row = adj + (size_t)i * DEG;
    for (int m = 0; m < l; m++)
        if (row[m] == b) return 1;
    return 0;
}

/* Random simple d-regular bipartite graph on sides [0,H) and [H,2H). */
static int gen_random(void) {
    int h = H;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < h; i++) P[i] = i;
        for (int i = h - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[i];
            P[i] = P[j];
            P[j] = t;
        }
        int ok = 0;
        for (int rt = 0; rt < 20 && !ok; rt++) {
            if (rt > 0) {
                for (int i = h - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = P[i];
                    P[i] = P[j];
                    P[j] = t;
                }
            }
            ok = 1;
            for (int i = 0; i < h; i++) {
                int tries = 0;
                while (conflict(i, l, P[i]) && tries < 4000) {
                    int j = rndint(h);
                    if (j != i && !conflict(j, l, P[i]) && !conflict(i, l, P[j])) {
                        int t = P[i];
                        P[i] = P[j];
                        P[j] = t;
                    }
                    tries++;
                }
                if (conflict(i, l, P[i])) {
                    ok = 0;
                    break;
                }
            }
        }
        if (!ok) return 0;
        for (int i = 0; i < h; i++) {
            adj[(size_t)i * DEG + l] = h + P[i];
            adj[(size_t)(h + P[i]) * DEG + l] = i;
        }
    }
    return 1;
}

static int pick_defect(void) {
    int cnt = 0, pick = -1;
    const int *bd = BD[ci];
    for (int v = 0; v < N2; v++) {
        if (bd[v] > 0) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

/* Anneal the current random graph. Returns 1 when cost reaches 0. */
static int attempt(int maxevals) {
    int64_t c = eval_buf(RB[ci], RB[ca], BD[ci]);
    if (c == 0) return 1;
    double T0 = 1.0 + 0.005 * (double)c;
    if (T0 > 10.0) T0 = 10.0;
    for (int t = 0; t < maxevals; t++) {
        if ((t & 7) == 0 && elapsed() > TL) {
            timed_out = 1;
            return 0;
        }
        double T = T0 * (1.0 - (double)t / maxevals) + 0.05;
        int a1 = 0, b1 = 0, a2 = 0, b2 = 0, ok = 0;
        for (int tries = 0; tries < 50 && !ok; tries++) {
            int v = -1;
            if (rnd01() < 0.6) v = pick_defect();
            if (v >= 0) {
                int k = rndint(DEG);
                if (v < H) {
                    a1 = v;
                    b1 = adj[(size_t)v * DEG + k];
                } else {
                    b1 = v;
                    a1 = adj[(size_t)v * DEG + k];
                }
            } else {
                a1 = rndint(H);
                b1 = adj[(size_t)a1 * DEG + rndint(DEG)];
            }
            a2 = rndint(H);
            b2 = adj[(size_t)a2 * DEG + rndint(DEG)];
            ok = (a1 != a2) && (b1 != b2) && !has_nb(a1, b2) && !has_nb(a2, b1);
        }
        if (!ok) continue;
        sw(a1, b1, a2, b2);
        int64_t c2 = eval_buf(RB[ca], RB[cs], BD[ca]);
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            int tmp = ci;
            ci = ca;
            ca = tmp;
            c = c2;
            if (c == 0) return 1;
        } else {
            sw(a1, b2, a2, b1);
        }
    }
    return 0;
}

static int attempt_h(int h) {
    H = h;
    N2 = 2 * h;
    W = (N2 + 63) / 64;
    timed_out = 0;
    if (!gen_random()) return 0;
    return attempt(EVALS);
}

static void save_best(int h) {
    bestH = h;
    memcpy(adjbest, adj, sizeof(int) * (size_t)(2 * h) * DEG);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    HMAXV = atoi(argv[5]);
    if (HMAXV > HMAX_CAP) HMAXV = HMAX_CAP;
    if (DEG < 3 || D_ < 3 || HMAXV < DEG + 1) {
        printf("0 0\n");
        return 0;
    }
    tstart = now_s();
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0x5851F42D4C957F2DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    int NMAXV = 2 * HMAXV;
    int WMAX = (NMAXV + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)NMAXV * DEG);
    adjbest = malloc(sizeof(int) * (size_t)NMAXV * DEG);
    P = malloc(sizeof(int) * (size_t)HMAXV);
    int okalloc = (adj != NULL) && (adjbest != NULL) && (P != NULL);
    for (int i = 0; i < 3; i++) {
        RB[i] = malloc(sizeof(uint64_t) * (size_t)NMAXV * WMAX);
        BD[i] = malloc(sizeof(int) * (size_t)NMAXV);
        if (!RB[i] || !BD[i]) okalloc = 0;
    }
    if (!okalloc) {
        printf("0 0\n");
        return 0;
    }
    ci = 0;
    ca = 1;
    cs = 2;
    bestH = 0;

    /* Find a starting size that can be repaired. */
    int h = HMAXV / 4;
    if (h < DEG + 1) h = DEG + 1;
    int ok = 0;
    while (elapsed() < TL) {
        ok = attempt_h(h);
        if (ok || timed_out) break;
        if (h <= DEG + 1) break;
        h = h * 3 / 4;
        if (h < DEG + 1) h = DEG + 1;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    save_best(h);

    /* Adaptive growth: success grows the step, failure halves it. */
    int hlo = h;
    int step = h / 4;
    if (step < 1) step = 1;
    while (elapsed() < TL && step >= 1) {
        int ht = hlo + step;
        if (ht > HMAXV) {
            if (hlo >= HMAXV) break;
            ht = HMAXV;
        }
        ok = attempt_h(ht);
        if (timed_out) break;
        if (ok) {
            hlo = ht;
            save_best(ht);
            step = step + step / 2 + 1;
        } else {
            step /= 2;
        }
    }

    int n = 2 * bestH;
    long long m = (long long)bestH * DEG;
    printf("%d %lld\n", n, m);
    for (int a = 0; a < bestH; a++)
        for (int k = 0; k < DEG; k++)
            printf("%d %d\n", a, adjbest[(size_t)a * DEG + k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (start candidates and calibration early returns).
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
# Main build.
# ----------------------------------------------------------------------------

_MAX_H = 6000  # per-side cap for the C engine (N <= 12000)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

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
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: random bipartite regular graphs repaired in C.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    remaining = budget - (time.monotonic() - t0)
    if d >= 3 and D >= 3 and remaining > 2.0:
        hmax = min(lib.moore_bound(d, D) // 2, _MAX_H)
        if hmax >= d + 1:
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, int(seed) & 0x7FFFFFFF, round(remaining - 1.0, 2), hmax],
                    timeout=remaining + 15.0,
                )
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    return best
