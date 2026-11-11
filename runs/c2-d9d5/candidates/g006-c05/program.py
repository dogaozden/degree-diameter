"""Multi-vertex voltage lifts over semidirect groups (bi-circulant base), searched by annealing.

Construction: take a group G = Z_n x| Z_k (r^k = 1 mod n) of order M and a base size B.
Left fibres L_0..L_{B-1} and right fibres R_0..R_{B-1} are each a copy of G. Slot s of left
fibre i has an offset off[s] in Z_B and a voltage v[i][s] in G, and joins L_{i,g} to
R_{i+off[s], g*v[i][s]}. Every vertex has degree d, the graph is bipartite, and left
multiplication by G is an automorphism that is transitive on each fibre. So diameter <= D
is decided by 2B BFS runs, one from each fibre representative. Simulated annealing moves
voltages and offsets. The graph has 2*B*M vertices; the target is half-order P = B*M >= 1249,
which beats the record 2496 for d=9, D=5.

The C engine binary-searches the ascending list of (B, group, r) candidates by P, then probes
upward. Python keeps the projective-plane, Araujo-Lopez and W(q) constructions and the K_{d,d}
fallback, and checks every returned graph with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex voltage lift search over Z_n x|_r Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo..hi bound P = B*M, the half-order. Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXP 10000
#define MAXV (2 * MAXP)
#define MAXD 32
#define MAXB 8
#define MAXGK 8
#define MAXCAND 100000

typedef struct { int B, gn, gk, r, P; } Cand;

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

/* ------------------------------------------------------------ group Z_gn x|_r Z_gk */

static int GN, GK, GM;
static int PW[MAXGK];

/* Element (a, b) is coded as a*GK + b. Product (a,b)(c,t) = (a + r^b c, b + t). */
static void set_group(int gn, int gk, int r) {
    GN = gn;
    GK = gk;
    GM = gn * gk;
    PW[0] = 1 % gn;
    for (int b = 1; b < gk; b++) PW[b] = (PW[b - 1] * r) % gn;
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, t = y - c * GK;
    int na = (a + PW[b] * c) % GN;
    int nb = (b + t) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int na = (GN - (PW[nb] * a) % GN) % GN;
    return na * GK + nb;
}

/* ------------------------------------------------------------ lift state */

static int B, M, P;
static int off[MAXD];
static int vv[MAXB][MAXD], vinv[MAXB][MAXD];
static int bestOff[MAXD], bestVv[MAXB][MAXD], bestVinv[MAXB][MAXD];
static int stamp_arr[MAXV], que[MAXV], stamp_ctr = 0;

static void setup_cand(const Cand *c) {
    B = c->B;
    set_group(c->gn, c->gk, c->r);
    M = GM;
    P = B * M;
}

/* Left vertex id i*M+g (0..P-1); right vertex id P + j*M + h.
 * Neighbour of v along slot s. */
static inline int nbr(int v, int s) {
    if (v < P) {
        int i = v / M, g = v - i * M;
        int j = (i + off[s]) % B;
        return P + j * M + gmul(g, vv[i][s]);
    } else {
        int w = v - P;
        int j = w / M, h = w - j * M;
        int i = (j - off[s] + B) % B;
        return i * M + gmul(h, vinv[i][s]);
    }
}

static int reach_count(int src) {
    int head = 0, tail = 0;
    stamp_ctr++;
    que[tail++] = src;
    stamp_arr[src] = stamp_ctr;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int s = 0; s < d; s++) {
                int u = nbr(v, s);
                if (stamp_arr[u] != stamp_ctr) {
                    stamp_arr[u] = stamp_ctr;
                    que[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2B fibre representatives of the vertices NOT within distance D. */
static long cost(void) {
    long c = 0;
    int V = 2 * P;
    for (int i = 0; i < B; i++) {
        c += V - reach_count(i * M);
        c += V - reach_count(P + i * M);
    }
    return c;
}

/* Voltage x at (i,s) is allowed iff no other slot with the same offset has voltage x at i. */
static int dup_free_slot(int i, int s, int x) {
    for (int t = 0; t < d; t++)
        if (t != s && off[t] == off[s] && vv[i][t] == x) return 0;
    return 1;
}

static int offset_ok(int s, int nt) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            if (t != s && off[t] == nt && vv[i][t] == vv[i][s]) return 0;
    return 1;
}

static int random_state(void) {
    for (int s = 0; s < d; s++) off[s] = s % B;
    for (int s = d - 1; s > 0; s--) {
        int t = rndint(s + 1);
        int tmp = off[s];
        off[s] = off[t];
        off[t] = tmp;
    }
    for (int i = 0; i < B; i++)
        for (int s = 0; s < d; s++) vv[i][s] = -1;
    for (int i = 0; i < B; i++)
        for (int s = 0; s < d; s++) {
            int ok = 0;
            for (int tries = 0; tries < 100000 && !ok; tries++) {
                int x = rndint(GM);
                if (dup_free_slot(i, s, x)) {
                    vv[i][s] = x;
                    vinv[i][s] = ginv(x);
                    ok = 1;
                }
            }
            if (!ok) return 0;
        }
    return 1;
}

/* Simulated annealing over voltages and offsets for the current candidate.
 * Returns 1 with cost 0 (diameter <= D) and leaves that state in place, 0 on timeout. */
static int search_cand(double until) {
    const int iters = 6000;
    while (now() < until) {
        if (!random_state()) return 0;
        long cur = cost();
        if (cur == 0) return 1;
        double c0 = (double)cur;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cur > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (B > 1 && rnd01() < 0.08) {
                int s = rndint(d), nt = rndint(B);
                if (nt == off[s] || !offset_ok(s, nt)) continue;
                int old = off[s];
                off[s] = nt;
                long c2 = cost();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else off[s] = old;
            } else {
                int i = rndint(B), s = rndint(d), x = rndint(GM);
                if (x == vv[i][s] || !dup_free_slot(i, s, x)) continue;
                int ov = vv[i][s], oi = vinv[i][s];
                vv[i][s] = x;
                vinv[i][s] = ginv(x);
                long c2 = cost();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else {
                    vv[i][s] = ov;
                    vinv[i][s] = oi;
                }
            }
        }
        if (cur == 0) return 1;
    }
    return 0;
}

static void save_best(void) {
    memcpy(bestOff, off, sizeof off);
    memcpy(bestVv, vv, sizeof vv);
    memcpy(bestVinv, vinv, sizeof vinv);
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static int valid_r(int r, int gn, int gk) {
    int one = 1 % gn;
    long x = one;
    for (int k = 0; k < gk; k++) x = x * r % gn;
    return x == one;
}

/* Candidates in ascending P = B*M. Each has B <= min(d, 8), gk <= 8, gn >= 2, M >= d. */
static void gen_cands(int lo, int hi) {
    nc = 0;
    for (int P_ = lo; P_ <= hi && nc < MAXCAND; P_++) {
        for (int Bq = 1; Bq <= d && Bq <= MAXB && nc < MAXCAND; Bq++) {
            if (P_ % Bq) continue;
            int Mm = P_ / Bq;
            if (Mm < d) continue;
            for (int gk = 1; gk <= MAXGK && gk <= Mm && nc < MAXCAND; gk++) {
                if (Mm % gk) continue;
                int gn = Mm / gk;
                if (gn < 2) continue;
                for (int r = 1; r < gn && nc < MAXCAND; r++) {
                    if (!valid_r(r, gn, gk)) continue;
                    cand[nc].B = Bq;
                    cand[nc].gn = gn;
                    cand[nc].gk = gk;
                    cand[nc].r = r;
                    cand[nc].P = P_;
                    nc++;
                }
            }
        }
    }
}

static void setup_for(int idx) { setup_cand(&cand[idx]); }

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
    double t0 = now();
    double budget = limit * 0.9 - 0.5;
    if (budget < 0.5) {
        printf("0 0\n");
        return 0;
    }
    t_end = t0 + budget;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 1) lo = 1;
    if (hi > MAXP) hi = MAXP;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }
    gen_cands(lo, hi);
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    double cap = budget * 0.3;

    /* Phase 1: binary search over the ascending candidate list. */
    int a = 0, b = nc - 1, best_idx = -1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        double rem = t_end - now();
        double slice = rem * 0.3;
        if (slice > cap) slice = cap;
        if (slice > rem) slice = rem;
        setup_for(mid);
        if (search_cand(now() + slice)) {
            best_idx = mid;
            save_best();
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: probe a few larger P values with the leftover time. */
    int fails = 0;
    int idx = best_idx + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        if (best_idx >= 0 && cand[idx].P <= cand[best_idx].P) {
            idx++;
            continue;
        }
        double rem = t_end - now();
        double slice = rem * 0.5;
        setup_for(idx);
        if (search_cand(now() + slice)) {
            best_idx = idx;
            save_best();
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
    setup_for(best_idx);
    memcpy(off, bestOff, sizeof off);
    memcpy(vv, bestVv, sizeof vv);
    memcpy(vinv, bestVinv, sizeof vinv);
    printf("%d %d\n", 2 * P, P * d);
    for (int i = 0; i < B; i++)
        for (int g = 0; g < M; g++)
            for (int s = 0; s < d; s++) {
                int u = i * M + g;
                int j = (i + off[s]) % B;
                int w = P + j * M + gmul(g, vv[i][s]);
                printf("%d %d\n", u, w);
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

    # Multi-vertex voltage lifts. P = B*M is half the order, so lo/hi are in P units.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
        lo = max(best[0] // 2 + 1, mb // 16)
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
