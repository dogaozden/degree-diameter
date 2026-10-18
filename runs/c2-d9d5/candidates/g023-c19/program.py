"""Multi-vertex voltage lifts over semidirect products Z_m x|_r Z_k.

Change from the parent: the search no longer uses single-base Haar graphs over
F_q x| H. Instead the base graph has b left and b right vertices and is d-regular,
given by d perfect matchings (layers t: left i -> right sigma_t(i)). Each dart
carries a voltage g in an arbitrary semidirect product Z_m x|_r Z_k, and the lift
joins (i,x) to (j, x*g). With b = 1 this reduces to the parent's family (cyclic and
semidirect Haar graphs), and b >= 2 gives new structure with 2bN vertices.

Diameter check: the group acts semiregularly on the left, so it suffices to run BFS
from the 2b base vertices (identity fibre elements) and count uncovered vertices.

Search: candidates (b, group) are sorted by vertex count and tried in ascending
order above the incumbent (a ladder). Each attempt is a simulated anneal over
voltages and layer permutations, followed by iterated restarts from the incumbent.
Collisions (parallel lift edges) are penalised so the output is always simple.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex voltage lifts over semidirect products Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit Vlo Vhi    (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 4
#define MAXD 16
#define MAXM (MAXB * MAXD)
#define MAXN 4800
#define MAXV 9600
#define MAXG 120000
#define MAXCAND 480000

typedef struct { int m, k, r, N; } Grp;
typedef struct { int V, key, gi, b; } Cand;

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

/* ------------------------------------------------------------ group Z_M x|_r Z_K
 * Element a*K + b, product (a,b)(c,e) = (a + r^b c, b + e). Needs r^K = 1 mod M. */

static int GM, GK, GN;
static int PW[MAXN];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    PW[0] = 1 % m;
    for (int i = 1; i < k; i++) PW[i] = (int)((long)PW[i - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + (int)((long)PW[b] * c % GM)) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (GM - (int)((long)PW[nb] * a % GM)) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ lift state */

static int B_;                       /* current base size b */
static int to_[MAXM], gv[MAXM];      /* dart e = t*b + i : left i -> right to_[e], voltage gv[e] */
static int fwd[MAXM][MAXN], bwd[MAXM][MAXN];
static int indart[MAXB][MAXD];       /* indart[j][t] = the dart in layer t that enters right j */
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_dart(int e, int g) {
    gv[e] = g;
    int gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        fwd[e][x] = gmul(x, g);
        bwd[e][x] = gmul(x, gi);
    }
}

/* Vertex id = u*N + x; u < b is left, u >= b is right. */
static int bfs_count(int src) {
    int b = B_, N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int u = v / N, x = v % N;
            if (u < b) {
                for (int t = 0; t < d; t++) {
                    int e = t * b + u;
                    int w = (b + to_[e]) * N + fwd[e][x];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            } else {
                int j = u - b;
                for (int t = 0; t < d; t++) {
                    int e = indart[j][t];
                    int w = (e % b) * N + bwd[e][x];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Zero iff the lift is simple and has diameter <= D. */
static long eval_cost(void) {
    int b = B_, N = GN, M = b * d, V = 2 * b * N;
    long pen = 0;
    for (int e = 0; e < M; e++)
        for (int f = e + 1; f < M; f++)
            if (e % b == f % b && to_[e] == to_[f] && gv[e] == gv[f]) pen++;
    for (int e = 0; e < M; e++) indart[to_[e]][e / b] = e;
    long unc = 0;
    for (int u = 0; u < 2 * b; u++) unc += (long)(V - bfs_count(u * N));
    return unc + pen * (long)V;
}

static void rand_state(void) {
    int b = B_, N = GN;
    for (int t = 0; t < d; t++) {
        int perm[MAXB];
        for (int i = 0; i < b; i++) perm[i] = i;
        for (int i = b - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < b; i++) to_[t * b + i] = perm[i];
    }
    for (int e = 0; e < b * d; e++) set_dart(e, rndint(N));
}

static void restore(const int *ito, const int *ig) {
    int M = B_ * d;
    for (int e = 0; e < M; e++) {
        to_[e] = ito[e];
        set_dart(e, ig[e]);
    }
}

/* One mutation, undoable with undo(). */
static int mk_kind, mk_e, mk_f, mk_old_g;
static void mutate(void) {
    int b = B_, N = GN, M = b * d;
    if (b >= 2 && rndint(4) == 0) {
        int t = rndint(d);
        int i1 = rndint(b), i2 = rndint(b - 1);
        if (i2 >= i1) i2++;
        int e1 = t * b + i1, e2 = t * b + i2;
        mk_kind = 1; mk_e = e1; mk_f = e2;
        int tmp = to_[e1]; to_[e1] = to_[e2]; to_[e2] = tmp;
    } else {
        int e = rndint(M);
        mk_kind = 0; mk_e = e; mk_old_g = gv[e];
        set_dart(e, rndint(N));
    }
}

static void undo(void) {
    if (mk_kind == 1) {
        int tmp = to_[mk_e]; to_[mk_e] = to_[mk_f]; to_[mk_f] = tmp;
    } else {
        set_dart(mk_e, mk_old_g);
    }
}

/* ------------------------------------------------------------ search */

static int inc_to[MAXM], inc_g[MAXM];
static int best_to[MAXM], best_g[MAXM];
static int best_m, best_k, best_r, best_b, best_V;

/* Iterated annealing: first round from random, later rounds from the incumbent
 * with two random mutations. Returns 1 when cost 0 is reached (state holds it). */
static int search(double until) {
    int M = B_ * d, have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            rand_state();
        } else {
            restore(inc_to, inc_g);
            mutate();
            mutate();
        }
        long cost = eval_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        const int iters = 6000;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            mutate();
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                undo();
            }
        }
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(inc_to, to_, sizeof(int) * (size_t)M);
            memcpy(inc_g, gv, sizeof(int) * (size_t)M);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ enumeration */

static Grp grps[MAXG];
static int ng = 0;
static Cand cands[MAXCAND];
static int nc = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int a, int e, int m) {
    long r = 1 % m, x = a % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static void addg(int m, int k, int r) {
    if (ng < MAXG) {
        grps[ng].m = m;
        grps[ng].k = k;
        grps[ng].r = r;
        grps[ng].N = m * k;
        ng++;
    }
}

static int cmp_cand(const void *a, const void *b_) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b_;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

static void print_best(void) {
    int b = best_b;
    set_group(best_m, best_k, best_r);
    int N = GN, M = b * d;
    printf("%d %d\n", 2 * b * N, M * N);
    for (int e = 0; e < M; e++) {
        int i = e % b, j = best_to[e];
        for (int x = 0; x < N; x++)
            printf("%d %d\n", i * N + x, (b + j) * N + gmul(x, best_g[e]));
    }
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
    int Vlo = atoi(argv[5]), Vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    B = MAXB;
    if (Vhi > MAXV) Vhi = MAXV;
    if (Vlo < 4) Vlo = 4;
    if (Vlo > Vhi) { printf("0 0\n"); return 0; }

    int Nlo = (Vlo + 2 * B - 1) / (2 * B);
    if (Nlo < 2) Nlo = 2;
    int Nhi = Vhi / 2;
    if (Nhi > MAXN) Nhi = MAXN;

    static int rtmp[2];
    for (int m = 2; m <= Nhi; m++) {
        int kmin = (Nlo + m - 1) / m;
        if (kmin < 1) kmin = 1;
        for (int k = kmin; (long)m * k <= Nhi; k++) {
            if (k == 1) { addg(m, 1, 1); continue; }
            int cnt = 0;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_i(r, k, m) != 1 % m) continue;
                if (cnt < 2) {
                    rtmp[cnt] = r;
                } else {
                    int j = rndint(cnt + 1);
                    if (j < 2) rtmp[j] = r;
                }
                cnt++;
            }
            for (int i = 0; i < cnt && i < 2; i++) addg(m, k, rtmp[i]);
        }
    }

    for (int gi = 0; gi < ng; gi++)
        for (int b = 1; b <= B; b++) {
            long V = 2L * b * grps[gi].N;
            if (V < Vlo || V > Vhi) continue;
            if (nc < MAXCAND) {
                cands[nc].V = (int)V;
                cands[nc].key = rndint(1 << 30);
                cands[nc].gi = gi;
                cands[nc].b = b;
                nc++;
            }
        }
    qsort(cands, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ladder: ascending vertex counts above the incumbent. At most 6 failed
     * attempts per vertex count, then move up. */
    int bestV = 0, curV = -1, fails = 0;
    for (int ci = 0; ci < nc; ci++) {
        Cand c = cands[ci];
        if (c.V <= bestV) continue;
        if (c.V != curV) { curV = c.V; fails = 0; }
        if (fails >= 6) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.15 * rem;
        if (slice < 0.6) slice = 0.6;
        if (slice > rem) slice = rem;
        int N = grps[c.gi].N;
        set_group(grps[c.gi].m, grps[c.gi].k, grps[c.gi].r);
        B_ = c.b;
        if (search(now() + slice)) {
            bestV = c.V;
            best_m = grps[c.gi].m;
            best_k = grps[c.gi].k;
            best_r = grps[c.gi].r;
            best_b = c.b;
            best_V = c.V;
            int M = c.b * d;
            memcpy(best_to, to_, sizeof(int) * (size_t)M);
            memcpy(best_g, gv, sizeof(int) * (size_t)M);
            (void)N;
        } else {
            fails++;
        }
    }

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

    # Search: multi-vertex voltage lifts over semidirect products, ascending ladder.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        vhi = min(mb, 9600)
        vlo = min(max(best[0] + 1, mb // 8), vhi)
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
