import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: unstructured search instead of symmetric lifts.
#
# The C engine works on an explicit d-regular bipartite graph with no imposed
# symmetry:
#   - start: a random d-regular bipartite graph on 2h vertices (h from Python),
#   - repair: simulated annealing with degree-preserving 2-switches, cost =
#     number of unordered vertex pairs at distance > D (bitset BFS),
#   - growth: when a graph is valid, insert new vertex pairs by splicing them
#     into random edges (degrees stay exact), then anneal again. The step size
#     doubles on success and halves on failure.
# The best valid graph is printed. Python re-checks it with lib.is_valid and
# keeps the K_{d,d} fallback and the exact PG(2,q) / W(q) constructions.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 400
#define PAT 120

static uint64_t rs;
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

static int DEG, DIAM, CAP, W;
static int N, NA, NB;
static int *adj, *Alist, *Blist;
static uint64_t *RA, *RB;
static int *gAdj, *gAlist, *gBlist;
static int gN, gNA, gNB, have_good;
static int *pbuf, *Pb, *Qb;
static double TL, tstart;
static int last_a1, last_b1, last_a2, last_b2, last_applied;

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double elapsed(void) {
    return now_s() - tstart;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    const int *av = adj + (size_t)a * DEG;
    for (int j = 0; j < DEG; j++)
        if (av[j] == b) return 1;
    return 0;
}

static void replace_in(int v, int old, int nw) {
    int *av = adj + (size_t)v * DEG;
    for (int j = 0; j < DEG; j++) {
        if (av[j] == old) {
            av[j] = nw;
            return;
        }
    }
}

/* Number of unordered pairs at distance > DIAM. */
static int64_t eval_cost(void) {
    uint64_t *R = RA, *T = RB;
    memset(R, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++)
        R[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *tv = T + (size_t)v * W;
            const uint64_t *rv = R + (size_t)v * W;
            memcpy(tv, rv, sizeof(uint64_t) * (size_t)W);
            const int *av = adj + (size_t)v * DEG;
            for (int j = 0; j < DEG; j++) {
                const uint64_t *ru = R + (size_t)av[j] * W;
                for (int w = 0; w < W; w++) tv[w] |= ru[w];
            }
            if (memcmp(tv, rv, sizeof(uint64_t) * (size_t)W) != 0) changed = 1;
        }
        uint64_t *tmp = R;
        R = T;
        T = tmp;
        if (!changed) break;
    }
    int64_t unreached = 0;
    for (int v = 0; v < N; v++) {
        int s = 0;
        const uint64_t *rv = R + (size_t)v * W;
        for (int w = 0; w < W; w++) s += popc(rv[w]);
        unreached += N - s;
    }
    return unreached / 2;
}

static int dup_slot(int v, int x, int upto) {
    const int *av = adj + (size_t)v * DEG;
    for (int k = 0; k < upto; k++)
        if (av[k] == x) return 1;
    return 0;
}

/* Random d-regular bipartite graph with h vertices per side (A = 0..h-1, B = h..2h-1). */
static int build_random(int h) {
    N = 2 * h;
    NA = h;
    NB = h;
    if (N > CAP) return 0;
    for (int i = 0; i < h; i++) {
        Alist[i] = i;
        Blist[i] = h + i;
    }
    for (size_t x = 0; x < (size_t)N * DEG; x++) adj[x] = -1;
    int *p = pbuf;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < h; i++) p[i] = i;
        for (int i = h - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < h; i++) {
            int tries = 0;
            while (tries < 200 && dup_slot(i, h + p[i], l)) {
                int j = rndint(h);
                if (j != i && !dup_slot(i, h + p[j], l) && !dup_slot(j, h + p[i], l)) {
                    int t = p[i];
                    p[i] = p[j];
                    p[j] = t;
                }
                tries++;
            }
            if (dup_slot(i, h + p[i], l)) return 0;
        }
        for (int i = 0; i < h; i++) {
            adj[(size_t)i * DEG + l] = h + p[i];
            adj[(size_t)(h + p[i]) * DEG + l] = i;
        }
    }
    return 1;
}

/* Degree-preserving 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int apply_switch(void) {
    last_applied = 0;
    if (NA < 2) return 0;
    int a1 = Alist[rndint(NA)], a2 = Alist[rndint(NA)];
    if (a1 == a2) return 0;
    int b1 = adj[(size_t)a1 * DEG + rndint(DEG)];
    int b2 = adj[(size_t)a2 * DEG + rndint(DEG)];
    if (b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    replace_in(a1, b1, b2);
    replace_in(b1, a1, a2);
    replace_in(a2, b2, b1);
    replace_in(b2, a2, a1);
    last_a1 = a1;
    last_b1 = b1;
    last_a2 = a2;
    last_b2 = b2;
    last_applied = 1;
    return 1;
}

static void undo_switch(void) {
    int a1 = last_a1, b1 = last_b1, a2 = last_a2, b2 = last_b2;
    replace_in(a1, b2, b1);
    replace_in(b2, a1, a2);
    replace_in(a2, b1, b2);
    replace_in(b1, a2, a1);
}

/* Add two vertices a (side A) and b (side B) by splicing them into DEG edges with
   distinct endpoints: (p,q) becomes (p,b) and (a,q). Degrees stay exact. */
static int insert_pair(void) {
    if (N + 2 > CAP || NA < 1) return 0;
    int cnt = 0, tries = 0;
    while (cnt < DEG && tries < 2000) {
        tries++;
        int p = Alist[rndint(NA)];
        int q = adj[(size_t)p * DEG + rndint(DEG)];
        int ok = 1;
        for (int k = 0; k < cnt; k++) {
            if (Pb[k] == p || Qb[k] == q) {
                ok = 0;
                break;
            }
        }
        if (ok) {
            Pb[cnt] = p;
            Qb[cnt] = q;
            cnt++;
        }
    }
    if (cnt < DEG) return 0;
    int a = N, b = N + 1;
    Alist[NA++] = a;
    Blist[NB++] = b;
    N += 2;
    for (int k = 0; k < DEG; k++) {
        int p = Pb[k], q = Qb[k];
        replace_in(p, q, b);
        replace_in(q, p, a);
        adj[(size_t)a * DEG + k] = q;
        adj[(size_t)b * DEG + k] = p;
    }
    return 1;
}

static int anneal(int iters, int patience) {
    int64_t cost = eval_cost();
    int64_t c0 = cost > 1 ? cost : 1;
    int64_t bestc = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 7) == 0 && elapsed() > TL) break;
        double T = 0.05 * (double)c0 * (1.0 - (double)t / iters) + 0.3;
        if (!apply_switch()) continue;
        int64_t c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                last = t;
            }
        } else {
            undo_switch();
        }
    }
    return cost == 0;
}

static void save_good(void) {
    memcpy(gAdj, adj, sizeof(int) * (size_t)N * DEG);
    memcpy(gAlist, Alist, sizeof(int) * (size_t)NA);
    memcpy(gBlist, Blist, sizeof(int) * (size_t)NB);
    gN = N;
    gNA = NA;
    gNB = NB;
    have_good = 1;
}

static void restore_good(void) {
    memcpy(adj, gAdj, sizeof(int) * (size_t)gN * DEG);
    memcpy(Alist, gAlist, sizeof(int) * (size_t)gNA);
    memcpy(Blist, gBlist, sizeof(int) * (size_t)gNB);
    N = gN;
    NA = gNA;
    NB = gNB;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    TL = atof(argv[5]);
    int h0 = atoi(argv[6]);
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DIAM < 1 || CAP < 2 * DEG + 4) {
        printf("0 0\n");
        return 0;
    }
    CAP -= CAP % 2;
    W = (CAP + 63) / 64;

    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    Alist = malloc(sizeof(int) * (size_t)CAP);
    Blist = malloc(sizeof(int) * (size_t)CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * W);
    gAdj = malloc(sizeof(int) * (size_t)CAP * DEG);
    gAlist = malloc(sizeof(int) * (size_t)CAP);
    gBlist = malloc(sizeof(int) * (size_t)CAP);
    pbuf = malloc(sizeof(int) * (size_t)CAP);
    Pb = malloc(sizeof(int) * (size_t)DEG);
    Qb = malloc(sizeof(int) * (size_t)DEG);
    if (!adj || !Alist || !Blist || !RA || !RB || !gAdj || !gAlist || !gBlist ||
        !pbuf || !Pb || !Qb) {
        printf("0 0\n");
        return 0;
    }

    int h = h0;
    if (h < DEG) h = DEG;
    if (2 * h > CAP) h = CAP / 2;
    int s = 1;
    have_good = 0;

    while (elapsed() < TL) {
        if (!have_good) {
            if (!build_random(h)) {
                h = h * 9 / 10;
                if (h < DEG) break;
                continue;
            }
            if (anneal(ITERS, PAT)) {
                save_good();
                s = 1;
            } else {
                h = h - h / 20 - 1;
                if (h < DEG) break;
            }
        } else {
            restore_good();
            int ok_ins = 1;
            for (int k = 0; k < s; k++) {
                if (!insert_pair()) {
                    ok_ins = 0;
                    break;
                }
            }
            if (!ok_ins) break;
            if (anneal(ITERS, PAT)) {
                save_good();
                s = s * 2 > 64 ? 64 : s * 2;
            } else {
                s = s / 2;
                if (s < 1) s = 1;
            }
        }
    }

    if (!have_good) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", gN, gNA * DEG);
    for (int i = 0; i < gNA; i++) {
        int a = gAlist[i];
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", a, gAdj[(size_t)a * DEG + j]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept as safe, strong starting points for calibration-style cases).
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
# Main build: exact constructions, then the unstructured C search, then checks.
# ----------------------------------------------------------------------------

_MAX_CAP = 12000  # bitset memory is CAP * CAP / 8 bytes per buffer; keep it modest


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        if remaining > 2.0:
            moore = lib.moore_bound(d, D)
            cap = min(moore, _MAX_CAP)
            cap -= cap % 2
            h0 = max(d, moore // 10)
            h0 = min(h0, cap // 2)
            if cap >= 2 * d + 4:
                try:
                    text = lib.run_c(C_SOURCE,
                                     [d, D, cap, int(seed) & 0x7FFFFFFF,
                                      round(remaining, 2), h0],
                                     timeout=remaining + 20.0)
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
