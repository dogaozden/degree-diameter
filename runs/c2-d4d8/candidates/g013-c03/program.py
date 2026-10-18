"""Bi-Cayley lifts with wide base multigraphs, searched by annealing over voltages and dart targets.

Different from the parent: instead of a 1- or 2-fibre base with random darts, each attempt
picks a fibre count p in 1..6 and a random metacyclic group Z_m x|_r Z_k of order N with
p*N >= goal/2. The base is a d-regular bipartite multigraph on p + p fibres, stored as d layers
of permutations. Moves change one voltage or swap the fibre targets of two darts, which keeps
every degree at d. Duplicate (fibre pair, voltage) triples are rejected, so the lift stays simple.

Objective: total number of (fibre identity, vertex) pairs at distance > D. Left multiplication
is an automorphism acting regularly on each fibre, so BFS from the 2p fibre identities decides
the diameter exactly. Any candidate that reaches zero is checked with the full bitset test.

Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}), runs the
C annealer with the record as target, and accepts the output only if lib.is_valid passes and it
is strictly larger. Otherwise the start graph is returned.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 6
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int d, D;
static long MOORE;
static long target_n = 0;
static double t_end;

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

static int gcd(int a, int b) {
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset ball expansion). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        badv[v] = n - c;
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= d); }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static Grp G;

static int gmul(const Grp *Gp, int x, int y) {
    int a = x / Gp->k, b = x % Gp->k, c = y / Gp->k, e = y % Gp->k;
    return (int)((a + (long)Gp->rp[b] * c) % Gp->m) * Gp->k + (b + e) % Gp->k;
}

static void set_group(int m, int k, int r) {
    G.m = m; G.k = k; G.r = r;
    G.rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G.rp[b] = (int)((long)G.rp[b - 1] * r % m);
}

/* Uniform random metacyclic group of order Nn (reservoir over all (m, r)). */
static int pick_group(int Nn) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= Nn; m++) {
        if (Nn % m) continue;
        int k = Nn / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 1; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    set_group(bm, bk, br);
    return 1;
}

/* Lift state: P fibres per side, group order N, ND = P*d darts (d layers of permutations). */
static int P, N, ND;
static int di[MAXDART], dj[MAXDART], dg[MAXDART];
static Graph cur, cand;
static long cur_bad;

/* Vertices: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (P+j)*N + x. */
static void build_lift(Graph *g) {
    int S = P * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= S); }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + gmul(&G, x, dg[t]));
}

static int dup_any(void) {
    for (int a = 0; a < ND; a++)
        for (int b = a + 1; b < ND; b++)
            if (di[a] == di[b] && dj[a] == dj[b] && dg[a] == dg[b]) return 1;
    return 0;
}

static int init_darts(void) {
    int t = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < P; i++) { di[t] = i; dj[t] = perm[i]; t++; }
    }
    for (int a = 0; a < ND; a++) {
        int ok = 0;
        for (int tries = 0; tries < 100000 && !ok; tries++) {
            dg[a] = rndint(N);
            ok = 1;
            for (int s = 0; s < a; s++)
                if (di[s] == di[a] && dj[s] == dj[a] && dg[s] == dg[a]) { ok = 0; break; }
        }
        if (!ok) return 0;
    }
    return 1;
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is an automorphism acting regularly on each fibre, so the diameter is at
 * most D iff BFS from the identity of every fibre reaches everything within D. */
static long orbit_bad(const Graph *g) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * P; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Anneal voltages and dart targets. Returns 1 if the lift reaches zero bad pairs. The state
 * (di, dj, dg) is always the last accepted one, so callers rebuild cand from it. */
static int anneal(long iters, double T0, double T1, double until) {
    build_lift(&cur);
    cur_bad = orbit_bad(&cur);
    if (cur_bad == 0) return 1;
    int oj[MAXDART], og[MAXDART];
    double lr = log(T1 / T0);
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double T = T0 * exp(lr * (double)it / (double)iters);
        memcpy(oj, dj, sizeof(int) * ND);
        memcpy(og, dg, sizeof(int) * ND);
        if (rndint(2) == 0) {
            int t = rndint(ND);
            dg[t] = rndint(N);
        } else {
            int t1 = rndint(ND), t2 = rndint(ND);
            if (t1 == t2) continue;
            int tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
        }
        if (dup_any()) {
            memcpy(dj, oj, sizeof(int) * ND);
            memcpy(dg, og, sizeof(int) * ND);
            continue;
        }
        build_lift(&cur);
        long nb = orbit_bad(&cur);
        if (nb <= cur_bad || rnd01() < exp((double)(cur_bad - nb) / T)) {
            cur_bad = nb;
            if (nb == 0) return 1;
        } else {
            memcpy(dj, oj, sizeof(int) * ND);
            memcpy(dg, og, sizeof(int) * ND);
        }
    }
    return cur_bad == 0;
}

/* Random restarts (new group, new darts, anneal) at fibre count p and group order Nn. */
static int attempt(Graph *best, int p, int Nn, double until) {
    if (Nn < d || Nn < 1) return 0;
    P = p;
    N = Nn;
    ND = p * d;
    while (now() < until) {
        if (!pick_group(N)) return 0;
        if (!init_darts()) continue;
        if (anneal(20000, 2.0, 0.05, until)) {
            build_lift(&cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                return 1;
            }
        }
    }
    return 0;
}

/* Target the record (or best + 2 when it is already reached), with random fibre counts. */
static void search(Graph *best, double until) {
    while (now() < until) {
        long goal = (target_n > (long)best->n) ? target_n : (long)best->n + 2;
        if (goal > MOORE || goal > MAXN) return;
        int p = 1 + rndint(MAXP);
        long Nl = (goal + 2L * p - 1) / (2L * p);
        if (Nl < d) Nl = d;
        if (2L * p * Nl > MOORE || 2L * p * Nl > MAXN) {
            p = 1;
            Nl = (goal + 1) / 2;
            if (Nl < d) Nl = d;
            if (2L * p * Nl > MOORE || 2L * p * Nl > MAXN) return;
        }
        double rem = until - now();
        if (rem <= 0) return;
        double sl = rem / 4.0;
        if (sl < 1.0) sl = 1.0;
        if (sl > rem) sl = rem;
        attempt(best, p, (int)Nl, now() + sl);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);

    if (d >= 2 && D >= 2 && best.n < MOORE) search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Best known orders (targets for the record-jump phase in C).
RECORDS = {(3, 3): 14, (4, 8): 2184}


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); the caller checks each with lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    try:
        cands = known_starts(d, D)
    except Exception:
        cands = []
    for n, e in cands:
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    target = RECORDS.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), target],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
