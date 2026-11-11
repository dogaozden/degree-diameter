"""Multi-orbit voltage lifts for the bipartite degree-diameter problem.

New idea in this version: the parent searches only Haar graphs, i.e. one orbit per side.
Here the graph has B left orbits L_i and B right orbits R_j, each a copy of a group G of
order N (G = F_q x| H or Z_N). Dart (t, i) joins L_i to R_{SIG[t][i]} with voltage V[t][i],
so L_{i,x} ~ R_{j, x*V}. Each SIG[t] is a permutation, which makes the base d-regular on
both sides. Two darts from the same i to the same j must have different voltages, or the
graph has parallel edges. This is handled by a penalty.

Left translations are automorphisms, so the diameter is decided by BFS from the 2B sources
L_{i,e} and R_{j,e}. The annealing cost is the number of unreached pairs over those sources,
plus 100 per voltage conflict. Moves change one voltage or re-draw one permutation row.
Candidates are tried in ascending total order, which climbs past the current best.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search.
 * Usage: prog d D seed time_limit lo hi maxB     (stdin ignored)
 * lo, hi bound the total vertex count 2*B*N.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXB 4
#define MAXD 16
#define MAXNG 3200
#define MAXV (2 * MAXB * MAXNG)
#define MAXCAND 60000

typedef struct { int kind, q, p, k, c; long N; int nb; long total; } Cand;

static int d, D, B;
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

/* ------------------------------------------------------------ groups */

static int GN, GC;
static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];
static int *MT = NULL;      /* MT[x*GN + y] = x*y */
static long MTcap = 0;
static int INV[MAXNG];

static void ensure_mt(int N) {
    long need = (long)N * N;
    if (need > MTcap) {
        int *nm = realloc(MT, sizeof(int) * (size_t)need);
        if (!nm) exit(1);
        MT = nm;
        MTcap = need;
    }
}

static inline int gmul_aff(int x, int y) {
    int a = x / GC, j = x - a * GC, b = y / GC, t = y - b * GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static void finish_group(int N) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* F_q x| H with H the subgroup of order c in F_q^*; element (a, h_j) coded a*c + j. */
static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    GC = c;
    int N = q * c;
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
    ensure_mt(N);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul_aff(x, y);
    finish_group(N);
}

static void setup_cyclic(int N) {
    ensure_mt(N);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = (x + y) % N;
    GC = 1;
    finish_group(N);
}

static void setup_cand(const Cand *c) {
    B = c->nb;
    if (c->kind == 0) setup_affine(c->q, c->p, c->k, c->c);
    else setup_cyclic((int)c->N);
}

/* ------------------------------------------------------------ lift state */

/* Dart (t, i): L_i -> R_{SIG[t][i]} with voltage V[t][i]. */
static int SIG[MAXD][MAXB], SIGINV[MAXD][MAXB], V[MAXD][MAXB];
static int bestSIG[MAXD][MAXB], bestV[MAXD][MAXB];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void random_perm_row(int t) {
    int a[MAXB];
    for (int i = 0; i < B; i++) a[i] = i;
    for (int i = B - 1; i > 0; i--) {
        int r = rndint(i + 1);
        int tmp = a[i]; a[i] = a[r]; a[r] = tmp;
    }
    for (int i = 0; i < B; i++) {
        SIG[t][i] = a[i];
        SIGINV[t][a[i]] = i;
    }
}

static void random_init(void) {
    for (int t = 0; t < d; t++) {
        if (B > 1) random_perm_row(t);
        else { SIG[t][0] = 0; SIGINV[t][0] = 0; }
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < B; i++)
            V[t][i] = rndint(GN);
}

/* Number of pairs of parallel darts (same i, same j, same voltage). */
static long conflicts(void) {
    long c = 0;
    for (int t = 0; t < d; t++)
        for (int t2 = t + 1; t2 < d; t2++)
            for (int i = 0; i < B; i++)
                if (SIG[t][i] == SIG[t2][i] && V[t][i] == V[t2][i]) c++;
    return c;
}

/* Number of vertices reached within D steps from src. */
static int bfs_reach(int src) {
    const int N = GN, BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int j = SIG[t][i];
                    int u = BN + j * N + MT[x * N + V[t][i]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int i = SIGINV[t][j];
                    int u = i * N + MT[y * N + INV[V[t][i]]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cost_all(void) {
    long NV2 = 2L * B * GN;
    long c = 0;
    for (int i = 0; i < B; i++) c += NV2 - bfs_reach(i * GN);
    for (int j = 0; j < B; j++) c += NV2 - bfs_reach(B * GN + j * GN);
    return c + 100L * conflicts();
}

/* Simulated annealing over voltages and permutation rows. Returns 1 at cost 0. */
static int anneal(double until, long iters) {
    while (now() < until) {
        random_init();
        long cost = cost_all();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (long it = 0; it < iters; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / (double)iters);
            if (B > 1 && rndint(100) < 10) {
                int t = rndint(d);
                int oldS[MAXB], oldI[MAXB];
                for (int i = 0; i < B; i++) {
                    oldS[i] = SIG[t][i];
                    oldI[i] = SIGINV[t][i];
                }
                random_perm_row(t);
                long c2 = cost_all();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    for (int i = 0; i < B; i++) {
                        SIG[t][i] = oldS[i];
                        SIGINV[t][i] = oldI[i];
                    }
                }
            } else {
                int t = rndint(d), i = rndint(B);
                int old = V[t][i];
                int x = rndint(GN);
                if (x == old) continue;
                V[t][i] = x;
                long c2 = cost_all();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else V[t][i] = old;
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

static int is_prime_l(long n) {
    if (n < 2) return 0;
    for (long f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
    return x->kind - y->kind;
}

static Cand cand[MAXCAND];
static int nc = 0;

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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    int maxB = atoi(argv[7]);
    if (maxB > MAXB) maxB = MAXB;
    if (maxB < 1) maxB = 1;
    double t0 = now();
    t_end = t0 + limit - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    /* Candidates: affine F_q x| H for every c | q-1 (c = 1 is the additive group),
     * and cyclic Z_N for composite N (primes are already covered by affine c = 1). */
    for (int b = 1; b <= maxB; b++) {
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                long tot = 2L * b * N;
                if (N > MAXNG || N < 2L * d || tot < lo || tot > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {0, q, p, k, c, N, b, tot};
                    cand[nc++] = cd;
                }
            }
        }
        long Nlo = (lo + 2L * b - 1) / (2L * b), Nhi = hi / (2L * b);
        if (Nlo < 2L * d) Nlo = 2L * d;
        if (Nhi > MAXNG) Nhi = MAXNG;
        for (long N = Nlo; N <= Nhi; N++) {
            if (is_prime_l(N)) continue;
            long tot = 2L * b * N;
            if (nc < MAXCAND) {
                Cand cd = {1, 0, 0, 0, 1, N, b, tot};
                cand[nc++] = cd;
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);
    /* Hint from earlier runs: the affine B = 1 candidate F_251 x| Z_5 (order 1255) is
     * the known Haar-lift source of the 2510 graph. Try it first when it is in range. */
    for (int ci = 0; ci < nc; ci++) {
        if (cand[ci].kind == 0 && cand[ci].nb == 1 && cand[ci].q == 251 && cand[ci].c == 5) {
            Cand tmp = cand[0]; cand[0] = cand[ci]; cand[ci] = tmp;
            break;
        }
    }

    long bestTotal = 0;
    int bestIdx = -1;
    Cand bestCand;
    memset(&bestCand, 0, sizeof bestCand);

    for (int pass = 0; pass < 1000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].total <= bestTotal) continue;
            double rem = t_end - now();
            if (rem < 0.5) break;
            tried = 1;
            double frac = (pass == 0 && ci == 0) ? 0.3 : 0.2;
            double slice = frac * rem;
            if (slice < 1.5) slice = 1.5;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (anneal(now() + slice, 6000)) {
                bestTotal = cand[ci].total;
                bestIdx = ci;
                bestCand = cand[ci];
                memcpy(bestSIG, SIG, sizeof(SIG));
                memcpy(bestV, V, sizeof(V));
            }
        }
        if (!tried || t_end - now() < 0.5) break;
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&bestCand);
    memcpy(SIG, bestSIG, sizeof(SIG));
    memcpy(V, bestV, sizeof(V));
    for (int t = 0; t < d; t++)
        for (int i = 0; i < B; i++)
            SIGINV[t][SIG[t][i]] = i;

    int N = GN;
    long NV = 2L * B * N;
    long E = (long)B * N * d;
    printf("%ld %ld\n", NV, E);
    for (int i = 0; i < B; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int j = SIG[t][i];
                int y = MT[x * N + V[t][i]];
                printf("%d %d\n", i * N + x, B * N + j * N + y);
            }
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

    # Multi-orbit voltage-lift search over total orders in (lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, (mb * 26) // 100)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, 4],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
