"""Multi-base voltage lifts over metacyclic and affine groups for the bipartite degree-diameter problem.

Construction: a base graph with A left and A right vertices (A = 1..4) and d layers. Each layer
is a random permutation pi_t of {0..A-1}, so the base multigraph is d-regular. A dart (t, i) joins
L_i to R_{pi_t(i)} with a voltage v in a finite group G. The lift has vertices (side, i, x), x in G,
and edges (L, i, x) -- (R, pi_t(i), x * v). Voltages from L_i to R_j are distinct, so the lift is
simple and d-regular. The group acts on the left by multiplication, so the diameter is at most D
iff a BFS from each (L, i, identity) reaches every vertex within D steps.

Groups: affine F_q x| H (H of order c >= 2 in F_q^*), and Z_m x|_r Z_k (cyclic when r = 1).
Search: simulated annealing over voltages, with a binary search over the vertex count and a
greedy phase above the best found. Python keeps the projective-plane, Araujo-Lopez, W(q) and
K_{d,d} baselines, and checks every returned graph with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over finite groups.
 * Usage: prog d D seed budget lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*A*|G|.
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 900
#define NMAX 1700
#define MAXA 4
#define MAXD 32
#define MAXCAND 200000
#define MAXV (2 * MAXA * NMAX)

typedef struct { int type, q, c, m, k, r, a, N, T; } Cand;

static int dg, dia;
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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
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

/* ------------------------------------------------------------ group tables */

static int GN;
static unsigned short MT[NMAX][NMAX];
static int IV[NMAX];
static int PWG[MAXQ], HH[MAXQ], hidx[MAXQ];
static int powr[NMAX];

/* Affine group: element (a, h_j) coded a*c + j, product (a,h_j)(b,h_t) = (a + h_j b, h_j h_t). */
static void build_affine(int q, int c) {
    int p, k;
    GN = 0;
    if (!factor_pp(q, &p, &k)) return;
    build_field(q, p, k);
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) return;
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        HH[t] = PWG[(t * step) % (q - 1)];
        hidx[HH[t]] = t;
    }
    GN = q * c;
    for (int x = 0; x < GN; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < GN; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[HH[j]][b]];
            int nj = hidx[MULT[HH[j]][HH[t]]];
            MT[x][y] = (unsigned short)(na * c + nj);
        }
    }
}

/* Semidirect Z_m x|_r Z_k: element (a, b) coded a*k + b, product (a + r^b c, b + d). */
static void build_semidirect(int m, int k, int r) {
    GN = m * k;
    powr[0] = 1 % m;
    for (int b = 1; b < k; b++) powr[b] = (powr[b - 1] * r) % m;
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, d = y % k;
            int na = (a + powr[b] * c) % m;
            int nb = (b + d) % k;
            MT[x][y] = (unsigned short)(na * k + nb);
        }
    }
}

static void build_inverses(void) {
    for (int x = 0; x < GN; x++) {
        IV[x] = 0;
        for (int y = 0; y < GN; y++)
            if (MT[x][y] == 0) { IV[x] = y; break; }
    }
}

static void build_group(const Cand *c) {
    if (c->type == 0) build_affine(c->q, c->c);
    else build_semidirect(c->m, c->k, c->r);
    build_inverses();
}

/* ------------------------------------------------------------ lift state */

/* Left vertices (i, x) have index i*GN + x; right vertices (j, y) have index A*GN + j*GN + y.
 * Dart (t, i) joins (L,i,x) to (R, Pm[t][i], x * Vm[t][i]).
 * Qm[t][j] is the left index i with Pm[t][i] = j. */
static int A_;
static int Pm[MAXD][MAXA], Qm[MAXD][MAXA], Vm[MAXD][MAXA];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int reach_from(int src) {
    int N = GN, AN = A_ * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < dia && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < AN) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < dg; t++) {
                    int j = Pm[t][i];
                    int y = MT[x][Vm[t][i]];
                    int u = AN + j * N + y;
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - AN;
                int j = w / N, y = w - j * N;
                for (int t = 0; t < dg; t++) {
                    int i = Qm[t][j];
                    int x = MT[y][IV[Vm[t][i]]];
                    int u = i * N + x;
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left multiplication is an automorphism, so BFS from each (L, i, identity) decides the diameter. */
static long cost_all(void) {
    long VT = 2L * A_ * GN, c = 0;
    for (int i0 = 0; i0 < A_; i0++)
        c += VT - reach_from(i0 * GN);
    return c;
}

/* True if voltage w for (t, i) clashes with an earlier layer t2 < lim that has the same target. */
static int conflict_ok(int t, int i, int w, int lim) {
    for (int t2 = 0; t2 < lim; t2++)
        if (t2 != t && Pm[t2][i] == Pm[t][i] && Vm[t2][i] == w) return 0;
    return 1;
}

static void init_state(void) {
    for (int t = 0; t < dg; t++) {
        int p[MAXA];
        for (int i = 0; i < A_; i++) p[i] = i;
        for (int i = A_ - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < A_; i++) {
            Pm[t][i] = p[i];
            Qm[t][p[i]] = i;
        }
    }
    for (int t = 0; t < dg; t++)
        for (int i = 0; i < A_; i++) {
            int w;
            do { w = rndint(GN); } while (!conflict_ok(t, i, w, t));
            Vm[t][i] = w;
        }
}

/* Simulated annealing over voltages with restarts. Returns 1 when the diameter is <= D. */
static int search_state(double until) {
    const int iters = 6000;
    while (now() < until) {
        init_state();
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(dg), i = rndint(A_);
            int old = Vm[t][i];
            int w;
            do { w = rndint(GN); } while (w == old || !conflict_ok(t, i, w, dg));
            Vm[t][i] = w;
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                cost = c2;
            else
                Vm[t][i] = old;
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cands[MAXCAND];
static int nc = 0;
static int tval[MAXCAND], tbeg[MAXCAND], tend_[MAXCAND];
static int nt = 0;

static int found = 0;
static int bestT = 0;
static Cand bestC;
static int bestP[MAXD][MAXA], bestV[MAXD][MAXA];

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->T != b->T) return a->T < b->T ? -1 : 1;
    return 0;
}

static int try_cand(int idx, double until) {
    Cand c = cands[idx];
    build_group(&c);
    if (GN < 2 * dg) return 0;
    A_ = c.a;
    if (!search_state(until)) return 0;
    if (!found || c.T > bestT) {
        found = 1;
        bestT = c.T;
        bestC = c;
        memcpy(bestP, Pm, sizeof Pm);
        memcpy(bestV, Vm, sizeof Vm);
    }
    return 1;
}

/* Try up to three random candidates with this total order, sharing the slice. */
static int probe_T(int ti, double slice) {
    int beg = tbeg[ti], end = tend_[ti];
    int cnt = end - beg;
    int tries = cnt < 3 ? cnt : 3;
    for (int s = 0; s < tries && now() < t_end; s++) {
        int idx = beg + rndint(cnt);
        if (try_cand(idx, now() + slice / tries)) return 1;
    }
    return 0;
}

static void print_best(void) {
    build_group(&bestC);
    A_ = bestC.a;
    memcpy(Pm, bestP, sizeof Pm);
    memcpy(Vm, bestV, sizeof Vm);
    int N = GN, AN = A_ * N;
    printf("%d %d\n", 2 * AN, AN * dg);
    for (int i = 0; i < A_; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < dg; t++) {
                int j = Pm[t][i];
                int y = MT[x][Vm[t][i]];
                printf("%d %d\n", i * N + x, AN + j * N + y);
            }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    dg = atoi(argv[1]);
    dia = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    t_end = now() + budget - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (dg < 2 || dg > MAXD || dia < 3) { printf("0 0\n"); return 0; }

    /* Affine groups F_q x| H, |H| = c >= 2. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N > NMAX || N < 2 * dg) continue;
            for (int a = 1; a <= MAXA; a++) {
                int T = 2 * a * N;
                if (T < lo || T > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {0, q, c, 0, 0, 0, a, N, T};
                    cands[nc++] = cd;
                }
            }
        }
    }

    /* Metacyclic groups Z_m x|_r Z_k with r^k = 1 mod m, gcd(r, m) = 1. */
    for (int m = 2; m <= NMAX; m++)
        for (int k = 1; m * k <= NMAX; k++) {
            int N = m * k;
            if (N < 2 * dg) continue;
            int anyT = 0;
            for (int a = 1; a <= MAXA; a++) {
                int T = 2 * a * N;
                if (T >= lo && T <= hi) anyT = 1;
            }
            if (!anyT) continue;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                for (int a = 1; a <= MAXA; a++) {
                    int T = 2 * a * N;
                    if (T < lo || T > hi) continue;
                    if (nc < MAXCAND) {
                        Cand cd = {1, 0, 0, m, k, r, a, N, T};
                        cands[nc++] = cd;
                    }
                }
            }
        }

    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cands, (size_t)nc, sizeof(Cand), cmp_cand);
    for (int i = 0; i < nc;) {
        int j = i;
        while (j < nc && cands[j].T == cands[i].T) j++;
        tval[nt] = cands[i].T;
        tbeg[nt] = i;
        tend_[nt] = j;
        nt++;
        i = j;
    }

    /* Phase 1: binary search over distinct totals. Each probe's slice is an equal share
     * of the remaining time over the probes still needed. */
    int ba = 0, bb = nt - 1, best_ti = -1;
    while (ba <= bb && now() < t_end) {
        int mid = (ba + bb) / 2;
        int span = bb - ba + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (probe_T(mid, slice)) {
            best_ti = mid;
            ba = mid + 1;
        } else {
            bb = mid - 1;
        }
    }

    /* Phase 2: spend the remaining time on the next totals above the best. */
    int ti = best_ti < 0 ? 0 : best_ti + 1;
    int fails = 0;
    while (ti < nt && now() < t_end && fails < 2) {
        if (found && tval[ti] <= bestT) { ti++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (probe_T(ti, slice)) {
            best_ti = ti;
            fails = 0;
        } else {
            fails++;
        }
        ti++;
    }

    if (!found) { printf("0 0\n"); return 0; }
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

    # Multi-base voltage lifts over affine and metacyclic groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = best[0] + 1
        hi = mb
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 5.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
