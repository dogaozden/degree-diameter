import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: grow a d-regular bipartite graph by vertex insertion + edge-swap
# annealing. The state is a simple d-regular bipartite graph on N + N vertices
# (A vertex i = id 2i, B vertex j = id 2j+1). A cost-0 state is a valid graph
# with diameter <= D. Moves:
#   * swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Keeps every degree and
#     bipartiteness. Cost = number of unordered vertex pairs at distance > D,
#     computed with bit-parallel ball expansion.
#   * insert: add one A and one B vertex. Choose d edges (a_i,b_i) with distinct
#     a_i and distinct b_i, delete them, and add (A_new,b_i) and (a_i,B_new).
#     All degrees stay d.
# Start: a regular graph on stdin if one is given (valid, d-regular, bipartite),
# otherwise a random d-regular bipartite graph. Then the engine repeatedly
# inserts a vertex pair and anneals; a failed attempt is rolled back to the last
# valid state. The best valid graph is printed in the usual text format.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 2600

static int DEG, DIAM, N;
static int *adj;
static uint64_t *bufA, *bufB;
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int have_best = 0, best_N = 0;
static int *best_adj, *snap;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(int v, int x) {
    const int *p = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++) if (p[k] == x) return 1;
    return 0;
}

static void rep(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int k = 0; k < DEG; k++) if (p[k] == old) { p[k] = nw; return; }
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long evalcost(void) {
    int n = 2 * N;
    size_t W = (size_t)((n + 63) >> 6);
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            const int *nb = adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *s2 = cur + (size_t)nb[k] * W;
                for (size_t w = 0; w < W; w++) {
                    uint64_t o = dst[w] | s2[w];
                    if (o != dst[w]) { dst[w] = o; changed = 1; }
                }
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *p = cur + (size_t)v * W;
        int c = 0;
        for (size_t w = 0; w < W; w++) c += pop64(p[w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Annealing with edge swaps. Returns the cost of the final state (the state is kept as is). */
static long long anneal(long long maxev, double Thi, double Tlo, long long cur) {
    double lr = log(Tlo / Thi);
    for (long long it = 0; it < maxev && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        double T = Thi * exp(lr * (double)it / (double)maxev);
        int a1 = 2 * rnd_int(N), a2 = 2 * rnd_int(N);
        if (a1 == a2) continue;
        int i = rnd_int(DEG), j = rnd_int(DEG);
        int b1 = adj[(size_t)a1 * DEG + i];
        int b2 = adj[(size_t)a2 * DEG + j];
        if (has(a1, b2) || has(a2, b1)) continue;
        rep(a1, b1, b2);
        rep(a2, b2, b1);
        rep(b1, a1, a2);
        rep(b2, a2, a1);
        long long c2 = evalcost();
        long long dl = c2 - cur;
        if (dl <= 0 || rnd_unit() < exp(-(double)dl / T)) {
            cur = c2;
        } else {
            rep(a1, b2, b1);
            rep(a2, b1, b2);
            rep(b1, a2, a1);
            rep(b2, a1, a2);
        }
    }
    return cur;
}

/* Random simple d-regular bipartite graph with n_side vertices per side. */
static int init_random(int n_side) {
    N = n_side;
    int *perm = malloc(sizeof(int) * (size_t)N);
    if (!perm) return 0;
    for (int i = 0; i < N; i++) perm[i] = i;
    for (int l = 0; l < DEG; l++) {
        int ok = 0;
        for (int tr = 0; tr < 100000 && !ok; tr++) {
            for (int i = N - 1; i > 0; i--) {
                int j = rnd_int(i + 1);
                int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
            }
            ok = 1;
            for (int i = 0; i < N && ok; i++) {
                int a = 2 * i, b = 2 * perm[i] + 1;
                for (int k = 0; k < l; k++)
                    if (adj[(size_t)a * DEG + k] == b) { ok = 0; break; }
            }
        }
        if (!ok) { free(perm); return 0; }
        for (int i = 0; i < N; i++) {
            int a = 2 * i, b = 2 * perm[i] + 1;
            adj[(size_t)a * DEG + l] = b;
            adj[(size_t)b * DEG + l] = a;
        }
    }
    free(perm);
    return 1;
}

/* Read a d-regular bipartite simple graph from stdin. Returns 1 on success. */
static int load_graph(void) {
    int n = 0, m = 0, ok = 0;
    int *eu = NULL, *ev = NULL, *deg = NULL, *off = NULL, *pos = NULL, *nbr = NULL;
    int *col = NULL, *qu = NULL, *newid = NULL, *fl = NULL;
    int c0 = 0, c1 = 0, i0 = 0, i1 = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || n > 2 * CAP || m > 2000000) return 0;
    eu = malloc(sizeof(int) * (size_t)m);
    ev = malloc(sizeof(int) * (size_t)m);
    deg = calloc((size_t)n, sizeof(int));
    off = malloc(sizeof(int) * (size_t)(n + 1));
    pos = malloc(sizeof(int) * (size_t)n);
    nbr = malloc(sizeof(int) * (size_t)(2 * m));
    col = malloc(sizeof(int) * (size_t)n);
    qu = malloc(sizeof(int) * (size_t)n);
    newid = malloc(sizeof(int) * (size_t)n);
    if (!eu || !ev || !deg || !off || !pos || !nbr || !col || !qu || !newid) goto done;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) goto done;
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) goto done;
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
    for (int v = 0; v < n; v++) if (deg[v] != DEG) goto done;
    off[0] = 0;
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    for (int v = 0; v < n; v++) pos[v] = off[v];
    for (int i = 0; i < m; i++) {
        nbr[pos[eu[i]]++] = ev[i];
        nbr[pos[ev[i]]++] = eu[i];
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail) {
            int u = qu[head++];
            for (int idx = off[u]; idx < off[u + 1]; idx++) {
                int w = nbr[idx];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qu[tail++] = w;
                } else if (col[w] == col[u]) {
                    goto done;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) { if (col[v] == 0) c0++; else c1++; }
    if (c0 != c1 || c0 < DEG + 1 || c0 > CAP) goto done;
    N = c0;
    for (int v = 0; v < n; v++)
        newid[v] = (col[v] == 0) ? 2 * (i0++) : 2 * (i1++) + 1;
    fl = calloc((size_t)(2 * N), sizeof(int));
    if (!fl) goto done;
    for (int i = 0; i < m; i++) {
        int x = newid[eu[i]], y = newid[ev[i]];
        if (fl[x] >= DEG || fl[y] >= DEG) goto done;
        for (int k = 0; k < fl[x]; k++) if (adj[(size_t)x * DEG + k] == y) goto done;
        adj[(size_t)x * DEG + fl[x]++] = y;
        adj[(size_t)y * DEG + fl[y]++] = x;
    }
    ok = 1;
done:
    free(eu); free(ev); free(deg); free(off); free(pos); free(nbr);
    free(col); free(qu); free(newid); free(fl);
    return ok;
}

/* Add one A vertex (id 2N) and one B vertex (id 2N+1) by the 6-edge trick. */
static int insert_vertex(void) {
    if (N >= CAP || N <= DEG) return 0;
    int *ca = malloc(sizeof(int) * (size_t)DEG);
    int *cb = malloc(sizeof(int) * (size_t)DEG);
    int *cs = malloc(sizeof(int) * (size_t)DEG);
    int ok = 0;
    for (int tr = 0; tr < 2000 && !ok; tr++) {
        for (int t = 0; t < DEG; t++) {
            int a2, dup;
            do {
                a2 = 2 * rnd_int(N);
                dup = 0;
                for (int s = 0; s < t; s++) if (ca[s] == a2) { dup = 1; break; }
            } while (dup);
            ca[t] = a2;
            cs[t] = rnd_int(DEG);
            cb[t] = adj[(size_t)a2 * DEG + cs[t]];
        }
        ok = 1;
        for (int t = 0; t < DEG && ok; t++)
            for (int s = 0; s < t; s++) if (cb[s] == cb[t]) { ok = 0; break; }
    }
    if (ok) {
        int An = 2 * N, Bn = 2 * N + 1;
        for (int t = 0; t < DEG; t++) {
            int a = ca[t], b = cb[t];
            adj[(size_t)a * DEG + cs[t]] = Bn;
            rep(b, a, An);
            adj[(size_t)An * DEG + t] = b;
            adj[(size_t)Bn * DEG + t] = a;
        }
        N++;
    }
    free(ca); free(cb); free(cs);
    return ok;
}

static void record_best(void) {
    best_N = N;
    memcpy(best_adj, adj, sizeof(int) * (size_t)2 * N * DEG);
    have_best = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [n0]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int N0 = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DIAM < 1 || DEG > 64) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    adj = malloc(sizeof(int) * (size_t)2 * CAP * DEG);
    size_t wmax = (size_t)((2 * CAP + 63) / 64);
    bufA = malloc(sizeof(uint64_t) * (size_t)2 * CAP * wmax);
    bufB = malloc(sizeof(uint64_t) * (size_t)2 * CAP * wmax);
    best_adj = malloc(sizeof(int) * (size_t)2 * CAP * DEG);
    snap = malloc(sizeof(int) * (size_t)2 * CAP * DEG);
    if (!adj || !bufA || !bufB || !best_adj || !snap) {
        printf("0 0\n");
        return 0;
    }

    if (!load_graph()) {
        if (N0 < DEG + 1) N0 = DEG + 1;
        if (N0 > CAP) N0 = CAP;
        if (!init_random(N0)) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cur = evalcost();
    while (cur > 0 && elapsed() < DEADLINE)
        cur = anneal(60000, 1.2, 0.08, cur);
    if (cur == 0) record_best();

    int fails = 0;
    while (have_best && elapsed() < DEADLINE) {
        int oldN = N;
        memcpy(snap, adj, sizeof(int) * (size_t)2 * oldN * DEG);
        if (!insert_vertex()) break;
        long long c = evalcost();
        long long evs = fails >= 4 ? 25000 : 3000;
        c = anneal(evs, 1.0, 0.08, c);
        if (c == 0) {
            record_best();
            fails = 0;
        } else {
            memcpy(adj, snap, sizeof(int) * (size_t)2 * oldN * DEG);
            N = oldN;
            fails++;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * best_N, best_N * DEG);
    for (int i = 0; i < best_N; i++) {
        for (int k = 0; k < DEG; k++) {
            int b = best_adj[(size_t)(2 * i) * DEG + k];
            printf("%d %d\n", i, best_N + (b - 1) / 2);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baseline constructions (valid fallbacks and regular starting graphs).
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


def _is_regular(g, d):
    """True if every vertex of g = (n, edges) has degree exactly d."""
    n, e = g
    if n <= 0:
        return False
    deg = [0] * n
    for u, v in e:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver: baselines, then the C vertex-insertion annealer seeded by the best
# regular baseline (or a random regular graph if none exists).
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    base = None

    def consider(g):
        nonlocal best, best_n
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def offer_base(g):
        nonlocal base
        if g is None or not _is_regular(g, d):
            return
        if not lib.is_valid(g[0], g[1], d, D):
            return
        if base is None or g[0] > base[0]:
            base = g
        consider(g)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            offer_base(pg)

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            offer_base(gq)

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    remaining = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if remaining >= 2.0:
        n0 = max(d + 1, 3 * d)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", n0],
                            stdin_graph=base, timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider((n, e))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
