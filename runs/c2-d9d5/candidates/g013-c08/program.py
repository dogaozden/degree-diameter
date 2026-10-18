"""Two-base voltage lifts over small semidirect groups for the bipartite degree-diameter problem.

Bold change: the parent searches only Haar graphs (one base vertex per side). This version
searches a second family in the same C engine: a 2-vertex base with voltages over a group
G = Z_m x|_r Z_s. Each left fibre and right fibre is a copy of G, and for t in 1..d/2 the
multiplicity matrix is [[t, d-t], [d-t, t]], so the lift is d-regular and simple (distinct
voltages inside each class). The lift has 4|G| vertices, and left translations act transitively
on each fibre, so diameter <= D reduces to 4 BFS runs (one per fibre representative).

Phase 1 is the parent's family (1-vertex base, Haar graphs over the same semidirect groups).
Phase 2 is the 2-vertex base. Both use iterated annealing on the voltages, with the cost being
the number of vertex pairs not yet within distance D. Every phase keeps the largest found
graph. Python keeps K_{d,d} and the projective-plane and Araujo-Pardo-Lopez constructions as
valid fallbacks, and checks the final output with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXDD 16
#define MAXDART (2 * MAXDD)
#define MAXGN 8192
#define MAXV (4 * MAXGN)
#define MAXCAND 256

static int d, D;
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

/* ------------------------------------------------------------ group Z_m x|_r Z_s */

static int GM, GS, GR, GN;
static int rp[MAXGN];   /* rp[b] = r^b mod m */

/* Element (a, b) is coded a*s + b; product (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int s, int r) {
    GM = m;
    GS = s;
    GR = r;
    GN = m * s;
    rp[0] = 1 % m;
    for (int b = 1; b < s; b++) rp[b] = (rp[b - 1] * r) % m;
}

static int mulg(int x, int y) {
    int a = x / GS, b = x % GS, c = y / GS, e = y % GS;
    int na = (a + rp[b] * c) % GM;
    int nb = b + e;
    if (nb >= GS) nb -= GS;
    return na * GS + nb;
}

static int invg(int x) {
    int a = x / GS, b = x % GS;
    int nb = (GS - b) % GS;
    int na = (GM - (rp[nb] * a) % GM) % GM;
    return na * GS + nb;
}

/* ------------------------------------------------------------ lift state */

static int K;            /* base size per side: 1 or 2 */
static int Dtot;         /* total darts = K*d */
static int dI[MAXDART], dJ[MAXDART], dV[MAXDART];
static int fwd[MAXDART][MAXGN], bwd[MAXDART][MAXGN];
static int Lidx[2][MAXDD], Ridx[2][MAXDD];
static int vis[MAXV], que[MAXV];
static int stampc = 0;
static int curT = 0, incT = 0;
static int incV[MAXDART];

static long best_nv = 0;
static int have_sol = 0;
static int sol_K, sol_m, sol_s, sol_r, sol_t;
static int sol_V[MAXDART];

/* Class (i,j) counts: K=1 -> d darts; K=2 -> t, d-t, d-t, t. */
static void set_layout(int t) {
    int cnt[2][2] = {{0, 0}, {0, 0}};
    if (K == 1) {
        cnt[0][0] = d;
    } else {
        cnt[0][0] = t;
        cnt[0][1] = d - t;
        cnt[1][0] = d - t;
        cnt[1][1] = t;
    }
    Dtot = K * d;
    int e = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int q = 0; q < cnt[i][j]; q++) {
                dI[e] = i;
                dJ[e] = j;
                e++;
            }
    int ln[2] = {0, 0}, rn[2] = {0, 0};
    for (int f = 0; f < Dtot; f++) {
        Lidx[dI[f]][ln[dI[f]]++] = f;
        Ridx[dJ[f]][rn[dJ[f]]++] = f;
    }
}

static void set_dart(int f) {
    int v = dV[f], iv = invg(v);
    for (int x = 0; x < GN; x++) {
        fwd[f][x] = mulg(x, v);
        bwd[f][x] = mulg(x, iv);
    }
}

static int class_conflict(int f, int v) {
    for (int g = 0; g < Dtot; g++)
        if (g != f && dI[g] == dI[f] && dJ[g] == dJ[f] && dV[g] == v) return 1;
    return 0;
}

static int pick_free(int f) {
    for (int tries = 0; tries < 100000; tries++) {
        int v = rndint(GN);
        if (!class_conflict(f, v)) return v;
    }
    return -1;
}

static void init_random(int t) {
    set_layout(t);
    for (int f = 0; f < Dtot; f++) dV[f] = -1;
    for (int f = 0; f < Dtot; f++) {
        int v, tries = 0;
        do {
            v = rndint(GN);
            tries++;
        } while (class_conflict(f, v) && tries < 100000);
        dV[f] = v;
    }
    for (int f = 0; f < Dtot; f++) set_dart(f);
}

/* ------------------------------------------------------------ cost */

/* Vertices: left (i,x) = i*GN + x; right (j,y) = K*GN + j*GN + y.
 * Edge (L_i,x) -- (R_j, x*v) for each dart (i,j,v). */
static int bfs_count(int src) {
    int LEFT = K * GN;
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < D; lvl++) {
        if (head == tail) break;
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < LEFT) {
                int i = v / GN, x = v - i * GN;
                for (int s = 0; s < d; s++) {
                    int f = Lidx[i][s];
                    int u = LEFT + dJ[f] * GN + fwd[f][x];
                    if (vis[u] != stampc) {
                        vis[u] = stampc;
                        que[tail++] = u;
                    }
                }
            } else {
                int w = v - LEFT;
                int j = w / GN, y = w - j * GN;
                for (int s = 0; s < d; s++) {
                    int f = Ridx[j][s];
                    int u = dI[f] * GN + bwd[f][y];
                    if (vis[u] != stampc) {
                        vis[u] = stampc;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Left translations act transitively on each fibre, so one BFS per fibre
 * representative decides the diameter. */
static long cover_cost(void) {
    long NVl = 2L * K * GN;
    long c = 0;
    for (int i = 0; i < K; i++) {
        c += NVl - bfs_count(i * GN);
        c += NVl - bfs_count(K * GN + i * GN);
    }
    return c;
}

/* ------------------------------------------------------------ annealing */

static int search_group(double until) {
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            int t = (K == 2) ? 1 + rndint(d / 2) : 0;
            curT = t;
            init_random(t);
        } else {
            curT = incT;
            set_layout(incT);
            for (int f = 0; f < Dtot; f++) dV[f] = incV[f];
            for (int f = 0; f < Dtot; f++) set_dart(f);
            for (int r = 0; r < 2; r++) {
                int f = rndint(Dtot);
                int v = pick_free(f);
                if (v >= 0) {
                    dV[f] = v;
                    set_dart(f);
                }
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int f = rndint(Dtot);
            int oldv = dV[f];
            int v = pick_free(f);
            if (v < 0) continue;
            dV[f] = v;
            set_dart(f);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                dV[f] = oldv;
                set_dart(f);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            incT = curT;
            memcpy(incV, dV, sizeof(int) * (size_t)Dtot);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* All groups Z_m x|_r Z_s with m*s = N (r^s = 1 mod m, gcd(r,m) = 1). */
static int enum_cands(int N, int *cm, int *cs, int *cr, int cap) {
    int nc = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int s = N / m;
        if (m == 1) {
            if (nc < cap) {
                cm[nc] = 1;
                cs[nc] = s;
                cr[nc] = 0;
                nc++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcdl(r, m) != 1) continue;
            if (powmodl(r, s, m) != 1) continue;
            if (nc < cap) {
                cm[nc] = m;
                cs[nc] = s;
                cr[nc] = r;
                nc++;
            }
        }
    }
    return nc;
}

static void shuffle3(int *a, int *b, int *c, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1), t;
        t = a[i]; a[i] = a[j]; a[j] = t;
        t = b[i]; b[i] = b[j]; b[j] = t;
        t = c[i]; c[i] = c[j]; c[j] = t;
    }
}

static void run_phase(int k, int lo, int hi, double phase_end, double slice_base) {
    for (int N = lo; N <= hi; N++) {
        if (now() >= phase_end) return;
        if (2L * k * N <= best_nv) continue;
        if (N < 2 * d) continue;
        int cm[MAXCAND], cs[MAXCAND], cr[MAXCAND];
        int nc = enum_cands(N, cm, cs, cr, MAXCAND);
        if (nc == 0) continue;
        shuffle3(cm, cs, cr, nc);
        int tried = 0;
        for (int c = 0; c < nc && tried < 4; c++) {
            double rem = phase_end - now();
            if (rem < 0.1) return;
            double slice = slice_base < rem ? slice_base : rem;
            tried++;
            K = k;
            setup_group(cm[c], cs[c], cr[c]);
            if (search_group(now() + slice)) {
                best_nv = 2L * k * N;
                have_sol = 1;
                sol_K = k;
                sol_m = cm[c];
                sol_s = cs[c];
                sol_r = cr[c];
                sol_t = curT;
                memcpy(sol_V, dV, sizeof(int) * (size_t)(k * d));
                break;
            }
        }
    }
}

static void print_solution(void) {
    K = sol_K;
    setup_group(sol_m, sol_s, sol_r);
    set_layout(sol_t);
    memcpy(dV, sol_V, sizeof(int) * (size_t)Dtot);
    for (int f = 0; f < Dtot; f++) set_dart(f);
    int n = 2 * K * GN, m = K * GN * d;
    printf("%d %d\n", n, m);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < GN; x++)
            for (int s = 0; s < d; s++) {
                int f = Lidx[i][s];
                printf("%d %d\n", i * GN + x, K * GN + dJ[f] * GN + fwd[f][x]);
            }
}

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo1 = atoi(argv[5]), hi1 = atoi(argv[6]);
    int lo2 = atoi(argv[7]), hi2 = atoi(argv[8]);
    best_nv = atol(argv[9]);
    if (d < 2 || d > MAXDD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (lo1 < 1) lo1 = 1;
    if (lo2 < 1) lo2 = 1;
    if (hi1 > MAXGN) hi1 = MAXGN;
    if (hi2 > MAXGN) hi2 = MAXGN;

    double t0 = now();
    double tend = t0 + limit * 0.9 - 0.5;
    double span = tend - t0;
    if (span < 0.5) {
        printf("0 0\n");
        return 0;
    }
    double split = t0 + 0.45 * span;
    double s1 = 0.05 * 0.45 * span;
    if (s1 < 1.0) s1 = 1.0;
    double s2 = 0.05 * 0.55 * span;
    if (s2 < 1.0) s2 = 1.0;

    run_phase(1, lo1, hi1, split, s1);
    run_phase(2, lo2, hi2, tend, s2);

    if (!have_sol) {
        printf("0 0\n");
        return 0;
    }
    print_solution();
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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        bn = best[0]
        # Phase 1: 1-vertex base (Haar graphs), vertices = 2N.
        lo1 = max(bn // 2 + 1, mb * 2 // 15)
        hi1 = mb // 2
        # Phase 2: 2-vertex base, vertices = 4N.
        lo2 = max(bn // 4 + 1, mb // 15)
        hi2 = mb // 4
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo1, hi1, lo2, hi2, bn],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
