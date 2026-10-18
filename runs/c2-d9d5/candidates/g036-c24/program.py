"""Multi-base affine voltage lifts for the bipartite degree-diameter problem.

Change from the parent: instead of one Haar graph on G = F_q x| H, this version
searches lifts of a base graph with kb L-vertices and kb R-vertices (kb = 1, 2, 3).
Base dart t = i*d + s joins L_i to R_{(i+s) mod kb}, so every base vertex has
degree d. Each dart carries a voltage in G, and the lift has 2*kb*|G| vertices:
L_(i,g) ~ R_(j, g*v_t) for dart t from i to j.

Left translation is an automorphism, so each base fibre is one orbit. Diameter
therefore reduces to 2*kb BFS runs, one from L_(i,e) and one from R_(j,e). The
search is simulated annealing over the voltages, with cost equal to the total
number of unreached (source, vertex) pairs. Parallel darts with equal voltage are
forbidden, so every returned graph is simple, bipartite and d-regular.

Candidates (kb, q, c) are sorted by vertex count and searched by binary search,
then by a short upward phase. The Python baselines (projective plane, Araujo-Lopez,
W(q), and K_{d,d}) remain as fallbacks, and every returned graph is checked with
lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base affine voltage lift search.
 * Usage: prog d D seed time_limit lo hi   (stdin ignored)
 * lo, hi bound the vertex count 2*kb*|G|.
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
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
#define MAXK 3
#define MAXT (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 8192

typedef struct { int q, p, k, c, N, kb, V; } Cand;

static int d, D, KB;
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

static int GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is index 0. */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
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

static int from_[MAXT], to_[MAXT];
static int incl[MAXK][MAXD], incn[MAXK];
static int volt[MAXT], bestVolt[MAXT];
static int fw[MAXT][MAXN], bw[MAXT][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart t = i*d + s goes from L_i to R_{(i+s) mod kb}. Each R_j gets exactly d darts. */
static void setup_base(int kb) {
    KB = kb;
    for (int j = 0; j < kb; j++) incn[j] = 0;
    for (int i = 0; i < kb; i++)
        for (int s = 0; s < d; s++) {
            int t = i * d + s;
            from_[t] = i;
            to_[t] = (i + s) % kb;
            int j = to_[t];
            incl[j][incn[j]++] = t;
        }
}

/* Vertices: L_(i,g) = i*N + g, R_(j,h) = KB*N + j*N + h.
 * L_(i,g) ~ R_(to, g*v), so R_(j,h) ~ L_(from, h*v^-1). */
static void set_dart(int t, int x) {
    volt[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[t][g] = gmul(g, x);
        bw[t][g] = gmul(g, xi);
    }
}

/* A new dart must not repeat the voltage of another dart on the same base pair. */
static int dup_ok(int t, int x) {
    int T = KB * d;
    for (int t2 = 0; t2 < T; t2++)
        if (t2 != t && from_[t2] == from_[t] && to_[t2] == to_[t] && volt[t2] == x)
            return 0;
    return 1;
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int N = GN, KN = KB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / N, g = v - i * N;
                for (int s = 0; s < d; s++) {
                    int t = i * d + s;
                    int u = KN + to_[t] * N + fw[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - KN;
                int j = w / N, h = w - j * N;
                for (int c = 0; c < incn[j]; c++) {
                    int t = incl[j][c];
                    int u = from_[t] * N + bw[t][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms, so one source per base vertex suffices. */
static long cover_cost(void) {
    int N = GN, KN = KB * N, V = 2 * KN;
    long c = 0;
    for (int i = 0; i < KB; i++) c += V - bfs_reach(i * N);
    for (int j = 0; j < KB; j++) c += V - bfs_reach(KN + j * N);
    return c;
}

/* Simulated annealing over the voltages. Returns 1 at cost 0, 0 on timeout. */
static int search_group(double until) {
    int N = GN, T = KB * d;
    const int iters = 6000;
    while (now() < until) {
        for (int t = 0; t < T; t++) volt[t] = -1;
        for (int t = 0; t < T; t++) {
            int x;
            do { x = rndint(N); } while (!dup_ok(t, x));
            volt[t] = x;
        }
        for (int t = 0; t < T; t++) set_dart(t, volt[t]);
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tmp = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(T);
            int x = rndint(N);
            if (x == volt[t] || !dup_ok(t, x)) continue;
            int old = volt[t];
            set_dart(t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tmp)) {
                cost = c2;
            } else {
                set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static int try_cand(const Cand *cd, double until) {
    setup_group(cd->q, cd->p, cd->k, cd->c);
    setup_base(cd->kb);
    return search_group(until);
}

static void print_result(void) {
    int N = GN, KN = KB * N, V = 2 * KN, T = KB * d;
    printf("%d %d\n", V, T * N);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < N; g++)
            printf("%d %d\n", from_[t] * N + g, KN + to_[t] * N + fw[t][g]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (hi > MAXV) hi = MAXV;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int kb = 1; kb <= MAXK; kb++)
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 2; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                int N = q * c;
                if (N > MAXN || N < 2 * d) continue;
                int V = 2 * kb * N;
                if (V < lo || V > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, N, kb, V};
                    cand[nc++] = cd;
                }
            }
        }
    /* Insertion sort by vertex count, ascending. */
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].V > t.V) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int best_idx = -1;

    /* Phase 1: binary search over the sorted candidates. Each probe gets an equal
     * share of the remaining time over the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_cand(&cand[mid], now() + slice)) {
            best_idx = mid;
            memcpy(bestVolt, volt, sizeof(int) * (size_t)(cand[mid].kb * d));
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few candidates above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    int bestV = best_idx < 0 ? 0 : cand[best_idx].V;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].V <= bestV) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (try_cand(&cand[idx], now() + slice)) {
            best_idx = idx;
            bestV = cand[idx].V;
            memcpy(bestVolt, volt, sizeof(int) * (size_t)(cand[idx].kb * d));
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    const Cand *cd = &cand[best_idx];
    setup_group(cd->q, cd->p, cd->k, cd->c);
    setup_base(cd->kb);
    for (int t = 0; t < cd->kb * d; t++) set_dart(t, bestVolt[t]);
    print_result();
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

    # Multi-base affine voltage lifts. Vertex count is 2*kb*|G|, so search a window
    # from just above the current best up to a third of the Moore bound.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 2, mb // 4)
        hi = max(lo + 2, mb // 3)
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
