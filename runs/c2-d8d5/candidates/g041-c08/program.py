"""Bipartite voltage-lift search over semidirect products, annealed on block representatives.

Left translations are automorphisms of a lift, so only 2p representative vertices need
to reach everything within D. The C engine anneals voltages and base-permutation swaps
against that reduced cost, then validates the full graph before returning it.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bipartite degree-diameter search: voltage lifts over semidirect products Z_m x| Z_k.
 * Left multiplication by the group is an automorphism of every lift, so the diameter
 * condition only needs the 2p block representatives. Simulated annealing moves voltages
 * and swaps base endpoints. Any graph returned is fully validated.
 * Usage:  prog d D seed time_limit      (stdin is ignored)
 * stdout: "n m" + edge lines.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXP 6
#define MAXG 512
#define MAXV (2 * MAXP * MAXG)
#define MAXN 8192
#define MAXC 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best, cand;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------------- generic graph utilities ---------------- */

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

static int gstamp[MAXN], gdist[MAXN], gq[MAXN];
static int gcur = 0;

static int graph_ball(const Graph *g, int src) {
    gcur++;
    int head = 0, tail = 0;
    gq[tail++] = src;
    gstamp[src] = gcur;
    gdist[src] = 0;
    while (head < tail) {
        int v = gq[head++];
        if (gdist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (gstamp[u] != gcur) {
                gstamp[u] = gcur;
                gdist[u] = gdist[v] + 1;
                gq[tail++] = u;
            }
        }
    }
    return tail;
}

static int graph_struct_ok(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int back = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) { back = 1; break; }
            if (!back) return 0;
        }
    }
    return 1;
}

static int graph_ok_full(const Graph *g) {
    if (!graph_struct_ok(g)) return 0;
    for (int v = 0; v < g->n; v++)
        if (graph_ball(g, v) != g->n) return 0;
    return 1;
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= d;
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            add_edge(g, a, d + b);
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* ---------------- groups Z_m x|_r Z_k ---------------- */

static int NN;                    /* group order in use */
static int MT[MAXG][MAXG];        /* multiplication table */
static int INV[MAXG];             /* inverses */
static int rp[MAXG];              /* r^b mod m */

static void setup_group(int m, int k, int r) {
    NN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++)
        rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < NN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < NN; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < NN; x++)
        for (int y = 0; y < NN; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

#define MAXCAND 4096
static int cm[MAXCAND], ck[MAXCAND], cr[MAXCAND];

static int enum_groups(int N) {
    int nc = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (nc < MAXCAND) { cm[nc] = 1; ck[nc] = k; cr[nc] = 0; nc++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nc < MAXCAND) { cm[nc] = m; ck[nc] = k; cr[nc] = r; nc++; }
        }
    }
    return nc;
}

/* ---------------- lift state ---------------- */

static int P_;                              /* base vertices per side */
static int nd;                              /* darts = d * P_ */
static int dI[MAXD * MAXP], dJ[MAXD * MAXP], dG[MAXD * MAXP];
static int DA[MAXP][MAXD], nA[MAXP], DB[MAXP][MAXD], nB[MAXP];
static int sJ[MAXD * MAXP], sG[MAXD * MAXP];

static int lstamp[MAXV], ldist[MAXV], lq[MAXV];
static int lcur = 0;

static int base_connected(void) {
    int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, cnt = 1;
    seen[0] = 1;
    stack[top++] = 0;
    while (top) {
        int v = stack[--top];
        for (int t = 0; t < nd; t++) {
            int a;
            if (v < P_) {
                if (dI[t] != v) continue;
                a = P_ + dJ[t];
            } else {
                if (dJ[t] != v - P_) continue;
                a = dI[t];
            }
            if (!seen[a]) { seen[a] = 1; cnt++; stack[top++] = a; }
        }
    }
    return cnt == 2 * P_;
}

static int dup_free(void) {
    for (int t = 0; t < nd; t++)
        for (int s = 0; s < t; s++)
            if (dI[t] == dI[s] && dJ[t] == dJ[s] && dG[t] == dG[s]) return 0;
    return 1;
}

static void init_state(int p) {
    P_ = p;
    nd = d * p;
    int perm[MAXP];
    do {
        for (int t = 0; t < d; t++) {
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) {
                dI[t * p + i] = i;
                dJ[t * p + i] = perm[i];
            }
        }
    } while (!base_connected());
    for (int t = 0; t < nd; t++) {
        for (;;) {
            dG[t] = rndint(NN);
            int clash = 0;
            for (int s = 0; s < t; s++)
                if (dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == dG[t]) { clash = 1; break; }
            if (!clash) break;
        }
    }
}

static void index_darts(void) {
    for (int i = 0; i < P_; i++) { nA[i] = 0; nB[i] = 0; }
    for (int t = 0; t < nd; t++) {
        DA[dI[t]][nA[dI[t]]++] = t;
        DB[dJ[t]][nB[dJ[t]]++] = t;
    }
}

/* Number of vertices within distance D of src in the lift (implicit adjacency). */
static int lift_ball(int src) {
    lcur++;
    int PN = P_ * NN;
    int head = 0, tail = 0;
    lq[tail++] = src;
    lstamp[src] = lcur;
    ldist[src] = 0;
    while (head < tail) {
        int v = lq[head++];
        int dv = ldist[v];
        if (dv >= D) continue;
        if (v < PN) {
            int i = v / NN, x = v % NN;
            for (int k = 0; k < nA[i]; k++) {
                int t = DA[i][k];
                int u = PN + dJ[t] * NN + MT[x][dG[t]];
                if (lstamp[u] != lcur) {
                    lstamp[u] = lcur;
                    ldist[u] = dv + 1;
                    lq[tail++] = u;
                }
            }
        } else {
            int w = v - PN, j = w / NN, y = w % NN;
            for (int k = 0; k < nB[j]; k++) {
                int t = DB[j][k];
                int u = dI[t] * NN + MT[y][INV[dG[t]]];
                if (lstamp[u] != lcur) {
                    lstamp[u] = lcur;
                    ldist[u] = dv + 1;
                    lq[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Sum over the 2p block representatives of vertices not reached within D.
 * Zero exactly when the lift has diameter <= D. */
static long eval_cost(void) {
    index_darts();
    long V = 2L * P_ * NN;
    long c = 0;
    for (int i = 0; i < P_; i++)
        c += V - lift_ball(i * NN);
    for (int j = 0; j < P_; j++)
        c += V - lift_ball((P_ + j) * NN);
    return c;
}

static int anneal(long steps) {
    long cur = eval_cost();
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) break;
        double T = 4.0 * (1.0 - (double)s / (double)steps) + 0.2;
        memcpy(sJ, dJ, sizeof(int) * (size_t)nd);
        memcpy(sG, dG, sizeof(int) * (size_t)nd);
        int t = rndint(nd);
        if (rndint(2) == 0) {
            dG[t] = rndint(NN);
        } else {
            int u = rndint(nd);
            if (u == t) continue;
            int tmp = dJ[t]; dJ[t] = dJ[u]; dJ[u] = tmp;
        }
        if (dup_free()) {
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                continue;
            }
        }
        memcpy(dJ, sJ, sizeof(int) * (size_t)nd);
        memcpy(dG, sG, sizeof(int) * (size_t)nd);
    }
    return cur == 0;
}

static void build_lift_graph(Graph *g) {
    int PN = P_ * NN;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= PN;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN; x++)
            add_edge(g, dI[t] * NN + x, PN + dJ[t] * NN + MT[x][dG[t]]);
}

static int lift_graph_ok(const Graph *g) {
    int reps[2 * MAXP], nr = 0;
    for (int i = 0; i < P_; i++) reps[nr++] = i * NN;
    for (int j = 0; j < P_; j++) reps[nr++] = (P_ + j) * NN;
    if (!graph_struct_ok(g)) return 0;
    for (int r = 0; r < nr; r++)
        if (graph_ball(g, reps[r]) != g->n) return 0;
    return 1;
}

static void lift_search(double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && fails < 5000) {
        long need = (long)best.n + 2;
        if (need > moore) break;
        int p = 2 + rndint(MAXP - 1);
        long N = (need + 2L * p - 1) / (2L * p) + rndint(3);
        if (N < d) N = d;
        if (N > MAXG || 2L * p * N > moore || 2L * p * N > MAXV) {
            fails++;
            continue;
        }
        int nc = enum_groups((int)N);
        if (nc == 0) { fails++; continue; }
        int c = rndint(nc);
        setup_group(cm[c], ck[c], cr[c]);
        init_state(p);
        fails = 0;
        if (anneal(3000)) {
            build_lift_graph(&cand);
            if (cand.n > best.n && lift_graph_ok(&cand))
                copy_graph(&best, &cand);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    if (t_end < t0 + 0.1) t_end = t0 + 0.1;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("1 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }

    best.n = 0;
    lift_search(t_end);
    if (best.n == 0 || !graph_ok_full(&best))
        complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search (C): representative-reduced voltage lifts over semidirect groups.
    c_budget = end - time.monotonic() - 0.5
    if D >= 2 and c_budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=None, timeout=c_budget + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
