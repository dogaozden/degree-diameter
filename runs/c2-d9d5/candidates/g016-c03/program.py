"""Circulant multi-orbit Haar lifts for the bipartite degree-diameter problem.

New idea in this version: the parent searches one-orbit Haar graphs on a group G of order N
(2N vertices). This version uses k orbits per side with a circulant base. Vertices are
L_{i,g} and R_{j,h}, with i, j in Z_k and g, h in G. Each L_{i,g} is joined to R_{i+r, g*t}
for t in T_r, where |T_r| = m_r and m_0 + ... + m_{k-1} = d. The graph has 2kN vertices and is
simple and d-regular.

Why it is cheap to check: the maps L_{i,g} -> L_{i,xg}, R_{j,h} -> R_{j,xh} (x in G) and the
shift i -> i+1, j -> j+1 are automorphisms. So every vertex can be moved to L_{0,e} or R_{0,e}.
The diameter test is therefore just two BFS runs, the same cost as the parent's one-orbit test.

The C engine tries orders n = 2kN (k = 1, 2, 3) with binary search over n, using the
parent's cyclic and F_q x| H groups. Annealing moves replace one connection element at a time
and update the adjacency incrementally. Time goes to restarts at the current search point.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Circulant multi-orbit Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Vertices: L_{i,g} = i*N+g, R_{j,h} = k*N + j*N + h.  i,j in Z_k, g,h in G.
 * L_{i,g} ~ R_{i+r, g*t} for t in T_r, |T_r| = m_r, sum_r m_r = d.
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
#define MAXN 2048
#define MAXD 32
#define MAXK 3
#define MAXV (2 * MAXK * MAXN)
#define ITERS 20000

typedef struct { int type, N, k, q, p, kf, c; } Opt;

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

/* ------------------------------------------------------------ groups */

/* Affine group F_q x| H, H the subgroup of order c in F_q^*. Element (a, h_j) = a*c + j. */
static int GC;
static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];

static void setup_affine(int q, int p, int kf, int c) {
    build_field(q, p, kf);
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

/* ------------------------------------------------------------ search state */

static int NN, KK, VV;
static uint16_t TB[MAXN * MAXN];   /* TB[x*NN + y] = x*y in G */
static int INV[MAXN];
static int OFF[MAXK], MB[MAXK];    /* bin r occupies slots OFF[r] .. OFF[r]+MB[r]-1 */
static int RR[MAXD];               /* slot -> bin */
static int X[MAXD];                /* connection elements, one per slot */
static int ADJ[MAXV * MAXD];
static int VIS[MAXV], QUE[MAXV];
static int STAMP = 0;

static void setup_opt(const Opt *o) {
    NN = o->N;
    KK = o->k;
    VV = 2 * KK * NN;
    if (o->type == 0) {
        for (int x = 0; x < NN; x++) {
            for (int y = 0; y < NN; y++)
                TB[x * NN + y] = (uint16_t)((x + y) % NN);
            INV[x] = (NN - x) % NN;
        }
    } else {
        setup_affine(o->q, o->p, o->kf, o->c);
        for (int x = 0; x < NN; x++) {
            for (int y = 0; y < NN; y++)
                TB[x * NN + y] = (uint16_t)gmul(x, y);
            INV[x] = ginv(x);
        }
    }
}

static void set_bins(const int *m) {
    int off = 0;
    for (int r = 0; r < KK; r++) {
        MB[r] = m[r];
        OFF[r] = off;
        for (int t = 0; t < m[r]; t++) RR[off + t] = r;
        off += m[r];
    }
}

/* Set slot s to element x and update the adjacency of all vertices in the affected orbits. */
static void set_elem(int s, int x) {
    X[s] = x;
    int r = RR[s];
    int ix = INV[x];
    for (int i = 0; i < KK; i++) {
        int jj = (i + r) % KK;
        int base = KK * NN + jj * NN;
        for (int g = 0; g < NN; g++)
            ADJ[(i * NN + g) * d + s] = base + TB[g * NN + x];
    }
    for (int j = 0; j < KK; j++) {
        int i = (j - r + KK) % KK;
        int base = i * NN;
        for (int h = 0; h < NN; h++)
            ADJ[(KK * NN + j * NN + h) * d + s] = base + TB[h * NN + ix];
    }
}

static int in_bin(int s, int x) {
    int r = RR[s], lo = OFF[r], hi = OFF[r] + MB[r];
    for (int s2 = lo; s2 < hi; s2++)
        if (X[s2] == x) return 1;
    return 0;
}

static void random_init(void) {
    for (int s = 0; s < d; s++) {
        int x;
        do {
            x = rndint(NN);
        } while (in_bin(s, x) && 0);
        /* Fill sequentially: reject elements already used in this bin among slots < s. */
        int r = RR[s], lo = OFF[r], ok;
        do {
            x = rndint(NN);
            ok = 1;
            for (int s2 = lo; s2 < s; s2++)
                if (X[s2] == x) { ok = 0; break; }
        } while (!ok);
        X[s] = x;
    }
    for (int s = 0; s < d; s++) set_elem(s, X[s]);
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    STAMP++;
    int head = 0, tail = 0;
    QUE[tail++] = src;
    VIS[src] = STAMP;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = QUE[head++];
            const int *a = ADJ + v * d;
            for (int s = 0; s < d; s++) {
                int u = a[s];
                if (VIS[u] != STAMP) { VIS[u] = STAMP; QUE[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Two BFS runs from L_{0,e} (index 0) and R_{0,e} (index KK*NN) decide the diameter. */
static long eval_cost(void) {
    int V = VV;
    return (long)(V - bfs_reach(0)) + (long)(V - bfs_reach(KK * NN));
}

static int anneal(double until) {
    long cost = eval_cost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    double Ts = 0.05 * c0 + 1.0, Te = 0.3;
    for (int it = 0; it < ITERS; it++) {
        if ((it & 15) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / ITERS);
        int s = rndint(d);
        int x;
        do { x = rndint(NN); } while (in_bin(s, x));
        int old = X[s];
        set_elem(s, x);
        long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            set_elem(s, old);
        }
    }
    return 0;
}

static void pick_m(int *m) {
    for (int r = 0; r < KK; r++) m[r] = 0;
    if (KK == 1 || rnd01() < 0.75) {
        int base = d / KK, extra = d % KK;
        int start = rndint(KK);
        for (int r = 0; r < KK; r++) m[r] = base;
        for (int u = 0; u < extra; u++) m[(start + u) % KK] += 1;
    } else {
        for (int u = 0; u < d; u++) m[rndint(KK)] += 1;
    }
}

/* Options for a target order n = 2kN: cyclic groups and affine groups, for k = 1, 2, 3. */
static int make_opts(int n, Opt *out, int maxout) {
    int cnt = 0;
    for (int k = 1; k <= MAXK; k++) {
        if (n % (2 * k)) continue;
        int N = n / (2 * k);
        if (N < 2 * d || N > MAXN) continue;
        if (cnt < maxout) {
            Opt o = {0, N, k, 0, 0, 0, 0};
            out[cnt++] = o;
        }
        for (int q = 3; q < MAXQ; q++) {
            int p, kf;
            if (N % q) continue;
            if (!factor_pp(q, &p, &kf)) continue;
            int c = N / q;
            if (c < 1 || (q - 1) % c) continue;
            if (cnt < maxout) {
                Opt o = {1, N, k, q, p, kf, c};
                out[cnt++] = o;
            }
        }
    }
    return cnt;
}

static Opt bestO;
static int bestM[MAXK];
static int bestX[MAXD];
static int bestN = 0;

/* Random restarts at order n until success or until time runs out. */
static int try_n(int n, double until) {
    Opt opts[64];
    int no = make_opts(n, opts, 64);
    if (no == 0) return 0;
    while (now() < until) {
        const Opt *o = &opts[rndint(no)];
        setup_opt(o);
        int m[MAXK];
        pick_m(m);
        set_bins(m);
        random_init();
        if (anneal(until)) {
            bestO = *o;
            memcpy(bestM, m, sizeof(int) * MAXK);
            memcpy(bestX, X, sizeof(int) * (size_t)d);
            bestN = 2 * KK * NN;
            return 1;
        }
    }
    return 0;
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > 2 * MAXN) hi = 2 * MAXN;
    if (lo < 4) lo = 4;
    if (hi < lo) { printf("0 0\n"); return 0; }

    /* Work in units of n/2: index x means order 2x. a is the known-valid index (from Python). */
    long a = (lo - 2) / 2;
    long b = hi / 2;

    while (a < b && now() < t_end - 0.5) {
        long mid = (a + b + 1) / 2;
        double rem = t_end - now();
        double slice = 0.2 * rem;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        if (try_n((int)(2 * mid), now() + slice))
            a = mid;
        else
            b = mid - 1;
    }
    /* Spend the remaining time just above the best order found. */
    while (now() < t_end - 0.5 && a + 1 <= hi / 2) {
        if (!try_n((int)(2 * (a + 1)), t_end)) break;
        a = a + 1;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_opt(&bestO);
    set_bins(bestM);
    for (int s = 0; s < d; s++) set_elem(s, bestX[s]);
    int L = KK * NN;
    printf("%d %d\n", VV, L * d);
    for (int v = 0; v < L; v++)
        for (int s = 0; s < d; s++)
            printf("%d %d\n", v, ADJ[v * d + s]);
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

    # Search: circulant multi-orbit Haar lifts (k = 1, 2, 3 orbits per side).
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = best[0] + 2
        hi = min(mb // 3, 4096)
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
