"""Two-orbit voltage lifts over cyclic and affine groups for the bipartite degree-diameter problem.

New idea in this version: the parent's Haar graphs have one orbit per side. Here the
C engine searches graphs with B = 1 or B = 2 orbits per side. Vertices are L(x,g) and
R(y,h) with x, y < B and g, h in a group G of order N. Each left orbit x has d slots,
and slot s joins L(x,g) to R(tgt_s, g*t_s). Targets are balanced so every right
vertex has degree d. The groups are cyclic Z_N or affine F_q x| Z_c with q prime.

Left multiplication is an automorphism of every orbit, so the diameter check needs
only one BFS per orbit, 2B runs in total. Moves change one voltage, or swap the
targets of two slots in the same row (B = 2 only). The C engine returns the largest
valid graph found, and Python checks it with lib.is_valid. The baselines (projective
planes, Araujo-Lopez, W(q), K_{d,d}) stay as fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search.
 * Usage: prog d D seed time_limit lo hi B     (stdin ignored)
 * B in {1,2} = number of orbits per side. Group order N in [lo,hi].
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXS 64
#define MAXV (4 * MAXN)
#define MAXCAND 16384

typedef struct { int type, q, c, N; } Cand;   /* type 0 = Z_N, type 1 = F_q x| Z_c */

static int d, D, BB, SL;
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

/* ------------------------------------------------------------ groups */

static int GT, GN, GQ, GC;
static int HV[MAXN];   /* HV[j] = h_j = g^(j*(q-1)/c) for the affine group */

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int is_prime_int(int n) {
    if (n < 2) return 0;
    for (int f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

static int find_prim(int q) {
    for (int g = 2; g < q; g++) {
        int x = 1, ord = 0;
        do {
            x = (int)((long)x * g % q);
            ord++;
        } while (x != 1 && ord < q);
        if (ord == q - 1) return g;
    }
    return 1;
}

static void setup_group(const Cand *cd) {
    GT = cd->type;
    GN = cd->N;
    if (GT == 0) return;
    GQ = cd->q;
    GC = cd->c;
    int g = find_prim(GQ);
    long step = (GQ - 1) / GC;
    long gs = powmod(g, step, GQ);
    long x = 1;
    for (int j = 0; j < GC; j++) {
        HV[j] = (int)x;
        x = x * gs % GQ;
    }
}

/* Element (a, j) is coded a*GC + j and means (a, h_j). Product (a,h_j)(b,h_t) = (a + h_j b, h_{j+t}). */
static inline int gop(int x, int y) {
    if (GT == 0) {
        int r = x + y;
        return r >= GN ? r - GN : r;
    }
    int a = x / GC, j = x - a * GC;
    int b = y / GC, t = y - b * GC;
    int na = (int)(((long)HV[j] * b + a) % GQ);
    int nt = j + t;
    if (nt >= GC) nt -= GC;
    return na * GC + nt;
}

static inline int ginv(int x) {
    if (GT == 0) return x ? GN - x : 0;
    int a = x / GC, j = x - a * GC;
    int jn = j ? GC - j : 0;
    int na = (GQ - (int)((long)HV[jn] * a % GQ)) % GQ;
    return na * GC + jn;
}

/* ------------------------------------------------------------ slots */

/* Slot s = x*d + j belongs to left orbit x. Its target orbit is ts[s] and its voltage is vo[s]. */
static int ts[MAXS], vo[MAXS];
static int fw[MAXS][MAXN], bw[MAXS][MAXN];   /* fw[s][g] = g*t, bw[s][h] = h*t^-1 */
static int inslot[2][MAXD];                   /* slots whose target is right orbit y */
static int bestTs[MAXS], bestVo[MAXS];

static void set_slot(int s, int t) {
    vo[s] = t;
    int ti = ginv(t);
    for (int g = 0; g < GN; g++) {
        fw[s][g] = gop(g, t);
        bw[s][g] = gop(g, ti);
    }
}

static void rebuild_inslot(void) {
    for (int y = 0; y < BB; y++) {
        int cnt = 0;
        for (int s = 0; s < SL && cnt < d; s++)
            if (ts[s] == y) inslot[y][cnt++] = s;
    }
}

/* Balanced targets. For B = 2, row 0 sends kk slots to orbit 0 and row 1 sends d-kk. */
static void set_pattern(int kk) {
    for (int s = 0; s < SL; s++) {
        int x = s / d, j = s % d;
        if (BB == 1) ts[s] = 0;
        else if (x == 0) ts[s] = (j < kk) ? 0 : 1;
        else ts[s] = (j < d - kk) ? 0 : 1;
    }
    rebuild_inslot();
}

/* True if giving slot s the voltage t collides with another slot of its row and target. */
static int conflict(int s, int t) {
    int x = s / d;
    for (int j = 0; j < d; j++) {
        int s2 = x * d + j;
        if (s2 == s) continue;
        if (ts[s2] == ts[s] && vo[s2] == t) return 1;
    }
    return 0;
}

static int row_ok(int x) {
    for (int j1 = 0; j1 < d; j1++)
        for (int j2 = j1 + 1; j2 < d; j2++) {
            int s1 = x * d + j1, s2 = x * d + j2;
            if (ts[s1] == ts[s2] && vo[s1] == vo[s2]) return 0;
        }
    return 1;
}

/* ------------------------------------------------------------ BFS and cost */

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, L = BB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < L) {
                int x = v / N, g = v - x * N;
                for (int j = 0; j < d; j++) {
                    int s = x * d + j;
                    int u = L + ts[s] * N + fw[s][g];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int r = v - L;
                int y = r / N, h = r - y * N;
                for (int m = 0; m < d; m++) {
                    int s = inslot[y][m];
                    int u = (s / d) * N + bw[s][h];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Sum over one source per orbit of the number of vertices not reached within D.
 * Left multiplication is an automorphism of each orbit, so these sources suffice. */
static long cost_all(void) {
    long V = 2L * BB * GN;
    long c = 0;
    for (int o = 0; o < 2 * BB; o++) {
        int src = (o < BB) ? o * GN : BB * GN + (o - BB) * GN;
        c += V - bfs_count(src);
    }
    return c;
}

/* ------------------------------------------------------------ search */

static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        int kk = (BB == 2) ? 1 + rndint(d - 1) : 0;
        set_pattern(kk);
        for (int s = 0; s < SL; s++) vo[s] = -1;
        for (int s = 0; s < SL; s++) {
            int t;
            do { t = rndint(N); } while (conflict(s, t));
            set_slot(s, t);
        }
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (BB == 2 && rnd01() < 0.25) {
                /* Target swap between two slots of one row. Counts per target are preserved. */
                int x = rndint(BB);
                int s1 = x * d + rndint(d), s2 = x * d + rndint(d);
                if (ts[s1] == ts[s2]) continue;
                int o1 = ts[s1], o2 = ts[s2];
                ts[s1] = o2;
                ts[s2] = o1;
                if (!row_ok(x)) {
                    ts[s1] = o1;
                    ts[s2] = o2;
                    continue;
                }
                rebuild_inslot();
                long c2 = cost_all();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    ts[s1] = o1;
                    ts[s2] = o2;
                    rebuild_inslot();
                }
            } else {
                /* Voltage change for one slot. */
                int s = rndint(SL);
                int t = rndint(N);
                if (t == vo[s] || conflict(s, t)) continue;
                int old = vo[s];
                set_slot(s, t);
                long c2 = cost_all();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_slot(s, old);
                }
            }
        }
        if (cost == 0) {
            memcpy(bestTs, ts, sizeof(int) * (size_t)SL);
            memcpy(bestVo, vo, sizeof(int) * (size_t)SL);
            return 1;
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN, V = 2 * BB * N;
    printf("%d %d\n", V, BB * N * d);
    for (int x = 0; x < BB; x++)
        for (int g = 0; g < N; g++)
            for (int j = 0; j < d; j++) {
                int s = x * d + j;
                printf("%d %d\n", x * N + g, BB * N + ts[s] * N + fw[s][g]);
            }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    return x->type - y->type;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    BB = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3 || (BB != 1 && BB != 2)) {
        printf("0 0\n");
        return 0;
    }
    SL = BB * d;
    if (SL > MAXS) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int N = lo; N <= hi && nc < MAXCAND; N++) {
        cand[nc].type = 0;
        cand[nc].q = 0;
        cand[nc].c = 0;
        cand[nc].N = N;
        nc++;
    }
    for (int q = 3; 2 * q <= hi; q++) {
        if (!is_prime_int(q)) continue;
        for (int c = 2; c < q; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                cand[nc].type = 1;
                cand[nc].q = q;
                cand[nc].c = c;
                cand[nc].N = (int)N;
                nc++;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search over sorted group orders. Each probe gets an equal share
     * of the remaining time, divided by the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) {
            span = (span + 1) / 2;
            probes++;
        }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(&cand[mid]);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) {
            idx++;
            continue;
        }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(&cand[idx]);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&cand[best_idx]);
    memcpy(ts, bestTs, sizeof(int) * (size_t)SL);
    for (int s = 0; s < SL; s++) set_slot(s, bestVo[s]);
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

    # Multi-orbit voltage lifts. B = 1 runs first (the single-orbit Haar family), then
    # B = 2 with the remaining time, using the best order found so far as its lower bound.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)

        def left():
            return 0.8 * time_limit - (time.monotonic() - t0) - 2.0

        for B, frac in ((1, 0.5), (2, 1.0)):
            budget = left() * frac
            if budget < 3.0:
                continue
            if B == 1:
                lo = max(best[0] // 2 + 1, mb // 8)
                hi = min(2048, mb // 2)
            else:
                lo = max(best[0] // 4 + 1, mb // 16)
                hi = min(2048, mb // 4)
            lo = max(lo, d)
            if lo > hi:
                continue
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, B],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
