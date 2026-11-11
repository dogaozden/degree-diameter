"""Combined affine and semidirect voltage-lift search for the bipartite degree-diameter problem.

Merges the two parents:
  * Candidate groups: affine groups F_q x| H (c | q-1, including c = 1) and general
    semidirect products Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1). Both are
    table-free after setup.
  * Lift family: K left orbits and K right orbits (K = 1, 2, 3), each right orbit
    receiving exactly d darts. K = 1 is the single-orbit Haar family of the first
    parent. Graphs have 2KN vertices, are d-regular and bipartite, and diameter
    <= D is checked with 2K BFS runs from orbit representatives.
  * Search: candidates are sorted by vertex count with random tie-breaks. A binary
    search finds the approximate frontier, then ascending passes retry candidates
    above the best count with fresh random starts, so no time is wasted.
"""
import time

import lib

C_SOURCE = r'''
/* Multi-orbit group voltage-lift search.
 * Usage: prog d D seed time_limit vlo vhi     (stdin ignored)
 * Candidates: 2*K*N vertices in [vlo, vhi], K in {1,2,3}, groups of order N.
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
 * Vertices: left L^a_x = a*N + x (a < K); right R^b_y = K*N + b*N + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 512
#define MAXC 512
#define MAXN 8192
#define MAXD 32
#define MAXK 3
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 60000

typedef struct { int type, a, b, r, K, N, V; uint32_t key; } Cand;

static int d, D, K, nd, GN;
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
static int PWG[MAXQ];
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

    int g = 1;
    for (int g0 = 1; g0 < q; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) { g = g0; break; }
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    built_q = q;
}

/* ------------------------------------------------------------ group law */

/* gtype 0: F_q x| H, element (a, h_j) coded a*GCc + j, h_j = g^(j*(q-1)/c).
 *          (a,h_j)(b,h_t) = (a + h_j b, h_j h_t).
 * gtype 1: Z_m x|_r Z_k, element (a, b) coded a*GK + b.
 *          (a,b)(c,e) = (a + r^b c, b + e). */
static int gtype = 0, GCc = 1, GM = 1, GK = 1;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC];
static int RP[MAXN];

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GCc, j = x % GCc, b = y / GCc, t = y % GCc;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GCc + HM[j * GCc + t];
    } else {
        int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
        int na = (a + RP[b] * c) % GM;
        int nb = (b + e) % GK;
        return na * GK + nb;
    }
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / GCc, j = x % GCc;
        int jn = (GCc - j) % GCc;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GCc + jn;
    } else {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        int na = (GM - (RP[nb] * a) % GM) % GM;
        return na * GK + nb;
    }
}

static void setup_cand(const Cand *cd) {
    K = cd->K;
    nd = K * d;
    if (cd->type == 0) {
        int q = cd->a, c = cd->b;
        int p = 0, kk = 0;
        factor_pp(q, &p, &kk);
        build_field(q, p, kk);
        gtype = 0;
        GCc = c;
        GN = q * c;
        int step = (q - 1) / c;
        for (int j = 0; j < q; j++) hidx[j] = -1;
        for (int t = 0; t < c; t++) {
            Hel[t] = PWG[(t * step) % (q - 1)];
            hidx[Hel[t]] = t;
        }
        for (int j = 0; j < c; j++)
            for (int t = 0; t < c; t++)
                HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
    } else {
        int m = cd->a, k = cd->b, r = cd->r;
        gtype = 1;
        GM = m;
        GK = k;
        GN = m * k;
        RP[0] = 1 % m;
        for (int b = 1; b < k; b++) RP[b] = (int)(((long)RP[b - 1] * r) % m);
    }
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD], cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static Cand bestCand;
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_dart(int t, int x) {
    vg[t] = x;
    int ix = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = gmul(g, x);
        invT[t][g] = gmul(g, ix);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

/* Each right orbit receives exactly d darts, so the graph is d-regular. */
static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

/* Duplicate darts (same left orbit, same target, same voltage) make repeated edges. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

static int bfs_count(int src) {
    int V2 = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / GN, x = v % GN;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * GN + fwdT[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each orbit, so one BFS per
 * orbit representative decides the diameter. */
static long cover_cost(void) {
    long V = 2L * K * GN;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * GN + b * GN);
    return c + 1000L * dup_count();
}

static void save_best(const Cand *cd) {
    bestCand = *cd;
    memcpy(bestTb, tb, sizeof(int) * (size_t)nd);
    memcpy(bestVg, vg, sizeof(int) * (size_t)nd);
}

static int search_cand(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            long c2;
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd);
                int x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int V = 2 * K * GN;
    printf("%d %d\n", V, K * GN * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * GN + tb[t] * GN + fwdT[t][x];
                printf("%d %d\n", a * GN + x, u);
            }
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(Cand c) {
    if (nc < MAXCAND) cand[nc++] = c;
}

static int cmp_cand(const void *A, const void *B) {
    const Cand *x = (const Cand *)A, *y = (const Cand *)B;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
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
    long vlo = atol(argv[5]), vhi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (vlo < 1) vlo = 1;
    if (vhi < vlo) { printf("0 0\n"); return 0; }

    /* Group orders N needed: 2*K*N in [vlo, vhi] for some K in 1..MAXK. */
    long Nmin = (vlo + 2 * MAXK - 1) / (2 * MAXK);
    long Nmax = vhi / 2;
    if (Nmin < d) Nmin = d;
    if (Nmax > MAXN) Nmax = MAXN;

    /* Affine groups F_q x| H, c | q-1 (c = 1 gives the additive group). */
    for (int q = 2; q < MAXQ; q++) {
        int p, kk;
        if (!factor_pp(q, &p, &kk)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < Nmin || N > Nmax) continue;
            for (int KK = 1; KK <= MAXK; KK++) {
                long V = 2L * KK * N;
                if (V < vlo || V > vhi) continue;
                Cand cd;
                cd.type = 0; cd.a = q; cd.b = c; cd.r = 0;
                cd.K = KK; cd.N = (int)N; cd.V = (int)V;
                cd.key = (uint32_t)rnd();
                add_cand(cd);
            }
        }
    }

    /* Semidirect products Z_m x|_r Z_k with m*k = N, m >= 2. */
    for (long N = Nmin; N <= Nmax; N++) {
        for (int kk = 1; kk <= N; kk++) {
            if (N % kk) continue;
            int m = (int)(N / kk);
            if (m < 2) continue;
            int pick = 1, cnt = 1;
            if (kk >= 2) {
                for (int r = 2; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod(r, kk, m) != 1 % m) continue;
                    cnt++;
                    if (rndint(cnt) == 0) pick = r;
                }
            }
            for (int KK = 1; KK <= MAXK; KK++) {
                long V = 2L * KK * N;
                if (V < vlo || V > vhi) continue;
                Cand cd;
                cd.type = 1; cd.a = m; cd.b = kk; cd.r = pick;
                cd.K = KK; cd.N = (int)N; cd.V = (int)V;
                cd.key = (uint32_t)rnd();
                add_cand(cd);
            }
        }
    }

    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestIdx = -1;
    long bestV = vlo - 1;

    /* Phase 1: binary search over the sorted candidates to find the frontier. */
    double p1_end = t0 + 0.45 * (t_end - t0);
    int li = 0, hi_i = nc - 1;
    while (li <= hi_i && now() < p1_end - 0.2) {
        int mid = (li + hi_i) / 2;
        double rem = p1_end - now();
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(&cand[mid]);
        if (search_cand(now() + slice)) {
            if (cand[mid].V > bestV) {
                bestV = cand[mid].V;
                bestIdx = mid;
                save_best(&cand[mid]);
            }
            li = mid + 1;
        } else {
            hi_i = mid - 1;
        }
    }

    /* Phase 2: ascending passes over candidates above the best; failed candidates
     * are retried with fresh random starts in later passes. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.5) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (search_cand(now() + slice)) {
                bestV = cand[ci].V;
                bestIdx = ci;
                save_best(&cand[ci]);
            }
        }
        if (!tried || t_end - now() < 0.5) break;
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&bestCand);
    memcpy(tb, bestTb, sizeof(int) * (size_t)nd);
    memcpy(vg, bestVg, sizeof(int) * (size_t)nd);
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, bestVg[t]);
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
    import itertools

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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        if best[0] < mb:
            budget = 0.9 * time_limit - (time.monotonic() - t0) - 3.0
            if budget > 2.0:
                # Window of vertex counts to search: from just above the current best
                # up to a fraction of the Moore bound, where the frontier lies.
                vlo = max(best[0] + 2, int(0.22 * mb))
                vhi = min(mb, int(0.42 * mb))
                if vlo <= vhi:
                    try:
                        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                         stdin_graph=None, timeout=budget + 8.0)
                        consider(lib.parse_graph_text(text))
                    except Exception:
                        pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
