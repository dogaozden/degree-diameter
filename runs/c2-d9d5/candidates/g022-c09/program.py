"""Multi-class voltage lifts over non-abelian groups for the bipartite degree-diameter problem.

Change in this version: instead of a single-class Haar graph on one group, the C engine
searches lifts of small bipartite base multigraphs with B classes per side (B = 1, 2, 3).
The base graph is circulant: left class i sends c_t darts to right class (i+t) mod B, with
sum c_t = d. A dart with voltage g joins (i,x) to (j, x*g). Left translations are
automorphisms, so the diameter is decided by BFS from the 2B class representatives.
Groups are either affine F_q x| H (as before) or semidirect products Z_m x|_r Z_k, which
give many more orders. Voltages are annealed to reach diameter <= D with no duplicate
edges. The Python side keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d}
baselines, and every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-class voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
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
#define MAXC 256
#define MAXN 2048
#define MAXD 32
#define MAXB 3
#define MAXDART (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 80000
#define DUPPEN 50

typedef struct { int type, b, q, p, k, c, m, kk, r, N, T; } Cand;

static int DEG, DIAM;
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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int base, int e, int m) {
    long r = 1 % m, b = base % m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return (int)r;
}

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

/* gtype 0: affine F_q x| H, element (a, h_j) coded a*GC + j.
 * gtype 1: Z_m x|_r Z_k, element (a, b) coded a*G1K + b. */
static int gtype = 0, GN = 0, GC = 1, GQ = 0, G1M = 1, G1K = 1, G1R = 0;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int RP[MAXN];
static int MT[MAXN * MAXN];
static int INVT[MAXN];

static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
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

static int gmul_raw(int x, int y) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    } else {
        int a = x / G1K, b = x % G1K, c = y / G1K, d = y % G1K;
        int na = (a + RP[b] * c) % G1M;
        int nb = (b + d) % G1K;
        return na * G1K + nb;
    }
}

static int ginv_raw(int x) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    } else {
        int a = x / G1K, b = x % G1K;
        int nb = (G1K - b) % G1K;
        int na = (G1M - (RP[nb] * a) % G1M) % G1M;
        return na * G1K + nb;
    }
}

/* ------------------------------------------------------------ graph state */

static int NB = 1, NDART = 1;
static int dvol[MAXDART], dinv[MAXDART], dleft[MAXDART], dright[MAXDART];
static int rlist[MAXDART], cpat[MAXB];

static Cand cand[MAXCAND];
static int nc = 0;

static void setup_cand(const Cand *cd) {
    NB = cd->b;
    NDART = NB * DEG;
    if (cd->type == 0) {
        gtype = 0;
        setup_group(cd->q, cd->p, cd->k, cd->c);
    } else {
        gtype = 1;
        G1M = cd->m;
        G1K = cd->kk;
        G1R = cd->r;
        RP[0] = 1 % G1M;
        for (int i = 1; i < G1K; i++)
            RP[i] = (int)((long)RP[i - 1] * G1R % G1M);
    }
    GN = cd->N;
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            MT[x * GN + y] = gmul_raw(x, y);
    for (int x = 0; x < GN; x++) INVT[x] = ginv_raw(x);
}

static void set_pattern(const int *pat) {
    for (int t = 0; t < NB; t++) cpat[t] = pat[t];
    int t = 0;
    for (int i = 0; i < NB; i++)
        for (int s = 0; s < NB; s++)
            for (int r = 0; r < cpat[s]; r++) {
                dleft[t] = i;
                dright[t] = (i + s) % NB;
                t++;
            }
    int cnt[MAXB];
    for (int j = 0; j < NB; j++) cnt[j] = 0;
    for (int t2 = 0; t2 < NDART; t2++) {
        int j = dright[t2];
        rlist[j * DEG + cnt[j]] = t2;
        cnt[j]++;
    }
}

static inline void set_vol(int t, int v) {
    dvol[t] = v;
    dinv[t] = INVT[v];
}

static void random_pattern(int *pat) {
    if (NB == 1) {
        pat[0] = DEG;
    } else if (NB == 2) {
        int p = 1 + rndint(DEG - 1);
        pat[0] = p;
        pat[1] = DEG - p;
    } else {
        int c0 = 1 + rndint(DEG - 2);
        int r = DEG - c0;
        int c1 = 1 + rndint(r - 1);
        pat[0] = c0;
        pat[1] = c1;
        pat[2] = r - c1;
    }
}

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Number of vertices within DIAM of the source vertex. */
static int reach_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < DIAM && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int cls = v / N, x = v - cls * N;
            if (cls < NB) {
                for (int s = 0; s < DEG; s++) {
                    int t = cls * DEG + s;
                    int u = (NB + dright[t]) * N + MT[x * N + dvol[t]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = cls - NB;
                for (int s = 0; s < DEG; s++) {
                    int t = rlist[j * DEG + s];
                    int u = dleft[t] * N + MT[x * N + dinv[t]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Cost 0 iff diameter <= DIAM (checked from every class representative,
 * which suffices by left-translation symmetry) and there are no duplicate edges. */
static long cost_eval(void) {
    int N = GN;
    long V = 2L * NB * N;
    long c = 0;
    for (int s = 0; s < 2 * NB; s++) c += V - reach_count(s * N);
    for (int i = 0; i < NB; i++)
        for (int a = 0; a < DEG; a++)
            for (int b2 = a + 1; b2 < DEG; b2++) {
                int ta = i * DEG + a, tb = i * DEG + b2;
                if (dright[ta] == dright[tb] && dvol[ta] == dvol[tb]) c += DUPPEN;
            }
    return c;
}

static int search_cand(double until) {
    const int iters = 8000;
    while (now() < until) {
        int pat[MAXB];
        random_pattern(pat);
        set_pattern(pat);
        for (int t = 0; t < NDART; t++) set_vol(t, rndint(GN));
        long cost = cost_eval();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(NDART);
            int old = dvol[t];
            set_vol(t, rndint(GN));
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_vol(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->T != y->T) return x->T < y->T ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (DEG < 2 || DEG > MAXD || DIAM < 2) { printf("0 0\n"); return 0; }
    if (lo < 4) lo = 4;
    if (hi > 2L * MAXB * MAXN) hi = 2L * MAXB * MAXN;

    nc = 0;
    for (int b = 1; b <= MAXB; b++) {
        if (b == 3 && DEG < 3) continue;
        for (long T = lo; T <= hi; T++) {
            if (T % (2 * b)) continue;
            int N = (int)(T / (2 * b));
            if (N < 2 || N > MAXN) continue;
            /* affine groups */
            for (int q = 3; q < MAXQ && q <= N; q++) {
                if (N % q) continue;
                int c = N / q;
                if (c < 2 || (q - 1) % c) continue;
                int p, k;
                if (!factor_pp(q, &p, &k)) continue;
                if (nc < MAXCAND) {
                    Cand cd = {0, b, q, p, k, c, 0, 0, 0, N, (int)T};
                    cand[nc++] = cd;
                }
            }
            /* semidirect groups Z_m x|_r Z_kk */
            for (int m = 1; m <= N; m++) {
                if (N % m) continue;
                int kk = N / m;
                int rmax = (m == 1) ? 1 : m;
                for (int r = 0; r < rmax; r++) {
                    if (m > 1 && gcd_int(r, m) != 1) continue;
                    if (powmod(r, kk, m) != 1 % m) continue;
                    if (nc < MAXCAND) {
                        Cand cd = {1, b, 0, 0, 0, 0, m, kk, r, N, (int)T};
                        cand[nc++] = cd;
                    }
                }
            }
        }
    }
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1, bestT = 0;
    int bestPat[MAXB];
    static int bestVol[MAXDART];

    /* Phase 1: binary search over candidates sorted by vertex count. Each probe
     * gets an equal share of the remaining time over the probes still needed. */
    int a = 0, bi = nc - 1;
    while (a <= bi && now() < t_end) {
        int mid = (a + bi) / 2;
        int span = bi - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(&cand[mid]);
        if (search_cand(now() + slice)) {
            if (cand[mid].T > bestT) {
                bestT = cand[mid].T;
                best_idx = mid;
                for (int t = 0; t < NB; t++) bestPat[t] = cpat[t];
                for (int t = 0; t < NDART; t++) bestVol[t] = dvol[t];
            }
            a = mid + 1;
        } else {
            bi = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few candidates above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].T <= bestT) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_cand(&cand[idx]);
        if (search_cand(now() + slice)) {
            bestT = cand[idx].T;
            best_idx = idx;
            for (int t = 0; t < NB; t++) bestPat[t] = cpat[t];
            for (int t = 0; t < NDART; t++) bestVol[t] = dvol[t];
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
    setup_cand(&cand[best_idx]);
    set_pattern(bestPat);
    for (int t = 0; t < NDART; t++) set_vol(t, bestVol[t]);
    int N = GN;
    printf("%d %d\n", 2 * NB * N, NDART * N);
    for (int t = 0; t < NDART; t++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", dleft[t] * N + x,
                   (NB + dright[t]) * N + MT[x * N + dvol[t]]);
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

    # Multi-class voltage lifts over non-abelian groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
