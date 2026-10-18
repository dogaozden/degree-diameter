"""Bi-Cayley lift search for the bipartite degree-diameter problem.

Change from the parent: the C engine now searches a new family alongside the
parent's Haar lifts. A bi-Cayley graph over G = F_q x| H (|G| = q*c) has two
orbits per side, so it has 4|G| vertices. Slots carry connection elements in
blocks (a,b), with a block matrix [[t, d-t], [d-t, t]], so each vertex has
degree d. Left translations preserve every orbit, so the diameter check needs
only 4 BFS runs, from L(0,e), L(1,e), R(0,e) and R(1,e).

The Haar lift (one orbit per side) is the same engine with nb = 1. It runs first
with 30% of the search time, so the parent's 2510-vertex result is kept as a
floor. The bi-Cayley phase then gets the rest of the time and only accepts orders
that beat the current best. All output is checked in Python with lib.is_valid,
and K_{d,d} is the fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley / Haar lift search over G = F_q x| H, |G| = q*c.
 * nb = 1: Haar graph (one orbit per side), |V| = 2|G|.
 * nb = 2: bi-Cayley graph (two orbits per side), |V| = 4|G|.
 * Usage: prog d D seed time_limit blo bhi hlo hhi   (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4096
#define MAXD 32
#define MAXV (4 * MAXN)
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static int d, D;
static double t_end;
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
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is index 0. */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

/* nb orbits per side. Vertices: L(a,g) = a*N+g; R(b,h) = nb*N + b*N + h.
 * Slot s joins L(blk_a[s], g) to R(blk_b[s], g*val[s]).
 * Slots in the same block (a,b) must have distinct values (simple graph). */
static int nb;
static int blk_a[MAXD], blk_b[MAXD], val[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_slot(int s, int x) {
    val[s] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[s][g] = gmul(g, x);
        bwd[s][g] = gmul(g, xi);
    }
}

static int val_free(int s, int x, int upto) {
    for (int t = 0; t < upto; t++)
        if (t != s && blk_a[t] == blk_a[s] && blk_b[t] == blk_b[s] && val[t] == x)
            return 0;
    return 1;
}

static void set_blocks(int t) {
    if (nb == 1) {
        for (int s = 0; s < d; s++) { blk_a[s] = 0; blk_b[s] = 0; }
        return;
    }
    int cnt = 0;
    for (int a = 0; a < 2; a++)
        for (int b = 0; b < 2; b++) {
            int k = (a == b) ? t : d - t;
            for (int j = 0; j < k; j++) {
                blk_a[cnt] = a;
                blk_b[cnt] = b;
                cnt++;
            }
        }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, base = nb * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < base) {
                int a = v / N, g = v % N;
                for (int s = 0; s < d; s++) {
                    if (blk_a[s] != a) continue;
                    int u = base + blk_b[s] * N + fwd[s][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - base, b = w / N, h = w % N;
                for (int s = 0; s < d; s++) {
                    if (blk_b[s] != b) continue;
                    int u = blk_a[s] * N + bwd[s][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit transitivity: one BFS per orbit representative decides the diameter. */
static long cover_cost(void) {
    int N = GN, V = 2 * nb * N;
    long c = 0;
    for (int a = 0; a < nb; a++) c += (long)(V - bfs_count(a * N));
    for (int b = 0; b < nb; b++) c += (long)(V - bfs_count(nb * N + b * N));
    return c;
}

/* Simulated annealing over the slot values. Returns 1 with a valid lift in
 * place when cost 0 is reached, 0 on timeout. */
static int search_engine(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        int t = (nb == 2) ? 1 + rndint(d - 1) : d;
        set_blocks(t);
        for (int s = 0; s < d; s++) {
            int x;
            do { x = rndint(N); } while (!val_free(s, x, s));
            set_slot(s, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int s = rndint(d);
            int x;
            do { x = rndint(N); } while (!val_free(s, x, d));
            int old = val[s];
            set_slot(s, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_slot(s, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best result */

static int bestV = 0;
static int b_nb, b_q, b_p, b_k, b_c;
static int b_val[MAXD], b_ba[MAXD], b_bb[MAXD];

static void save_best(void) {
    bestV = 2 * nb * GN;
    b_nb = nb;
    b_q = GQ; b_c = GC;
    b_p = 0; b_k = 0;
    for (int s = 0; s < d; s++) {
        b_val[s] = val[s];
        b_ba[s] = blk_a[s];
        b_bb[s] = blk_b[s];
    }
}

static void print_best(void) {
    int p = 0, k = 0;
    /* Recover p, k for the field of size b_q. */
    for (int f = 2; f <= b_q; f++) {
        if (b_q % f) continue;
        p = f;
        break;
    }
    if (!p) p = b_q;
    int r = b_q;
    k = 0;
    while (r % p == 0) { r /= p; k++; }
    setup_group(b_q, p, k, b_c);
    nb = b_nb;
    for (int s = 0; s < d; s++) {
        blk_a[s] = b_ba[s];
        blk_b[s] = b_bb[s];
        set_slot(s, b_val[s]);
    }
    int N = GN, base = nb * N;
    printf("%d %ld\n", 2 * base, (long)nb * N * d);
    for (int a = 0; a < nb; a++)
        for (int g = 0; g < N; g++)
            for (int s = 0; s < d; s++) {
                if (blk_a[s] != a) continue;
                printf("%d %d\n", a * N + g, base + blk_b[s] * N + fwd[s][g]);
            }
}

/* ------------------------------------------------------------ candidate phases */

static Cand cand[MAXCAND];

static void sort_cands(int nc) {
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }
}

static int build_cands(int lo, int hi) {
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi || N > MAXN) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    sort_cands(nc);
    return nc;
}

/* Ascending passes over candidates whose vertex count beats bestV. Each attempt
 * gets 20% of the remaining phase time (at least 1 s). Failed candidates are
 * retried with fresh random starts on later passes. */
static void run_phase(int nbv, int lo, int hi, double until) {
    int nc = build_cands(lo, hi);
    nb = nbv;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (2 * nb * cand[ci].N <= bestV) continue;
            double rem = until - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
            if (search_engine(now() + slice)) save_best();
        }
        if (!tried || until - now() < 0.3) break;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int blo = atoi(argv[5]), bhi = atoi(argv[6]);
    int hlo = atoi(argv[7]), hhi = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (bhi > MAXN) bhi = MAXN;
    if (hhi > MAXN) hhi = MAXN;

    double U = t_end - t0;
    /* Haar lifts first (the parent's safe floor), then bi-Cayley with the rest. */
    run_phase(1, hlo, hhi, t0 + 0.3 * U);
    run_phase(2, blo, bhi, t_end);

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    print_best();
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Search: Haar lifts (safe floor) and bi-Cayley lifts (new family).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        hlo = max(best[0] // 2 + 1, mb // 8)
        hhi = mb // 3
        blo = max(best[0] // 4 + 1, mb // 32)
        bhi = mb // 10
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), blo, bhi, hlo, hhi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
