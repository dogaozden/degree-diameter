"""Bi-Cayley (Haar) search over nonabelian linear groups, with the parent's algebraic starts as fallback.

New construction: for a finite group G of order N, the bipartite graph with parts G x {A}, G x {B} and
edges a_x ~ b_{x s} for s in S (|S| = d) is d-regular and bipartite, and left multiplication is an
automorphism transitive on each side. Its diameter is therefore at most D iff BFS from a_e and b_e
reaches all 2N vertices within D steps, which makes the check exact and cheap. C searches connection
sets S in SL(2,q), PSL(2,q), PGL(2,q) (q prime, q <= 17) by annealing that count, in ascending order of
order, and keeps the largest valid result. Python's algebraic starts are the fallback, so every case
returns a valid graph. Whether a record is beaten is not guaranteed.
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

#define MAXV 6600
#define MAXG 3300
#define MAXD 32
#define MAXW (MAXV / 64 + 1)
#define MAXQ4 83521

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

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

static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];

/* Number of unordered pairs at distance > D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXV) return 0;
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

static int queue_buf[MAXV];

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue_buf[tail++] = s;
        while (head < tail) {
            int v = queue_buf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue_buf[tail++] = u; }
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

/* ---- Linear groups: type 0 = SL(2,q), 1 = PSL(2,q), 2 = PGL(2,q), q prime <= 17. ---- */

static unsigned short mt[MAXG][MAXG];
static int inv_[MAXG];
static int gN, gid;
static int rep_of[MAXQ4], idx_of[MAXQ4];
static int ea[MAXG], eb[MAXG], ec[MAXG], ee[MAXG];

static int imod(int a, int q) { a %= q; return a < 0 ? a + q : a; }
static int enc(int a, int b, int c, int e, int q) { return ((a * q + b) * q + c) * q + e; }

static int build_linear(int type, int q) {
    int Q4 = q * q * q * q;
    if (Q4 > MAXQ4) return 0;
    for (int M = 0; M < Q4; M++) idx_of[M] = -1;
    for (int M = 0; M < Q4; M++) {
        int e = M % q, c = (M / q) % q, b = (M / (q * q)) % q, a = M / (q * q * q);
        int det = imod(a * e - b * c, q);
        int ok = (type == 2) ? (det != 0) : (det == 1);
        if (!ok) { rep_of[M] = -1; continue; }
        int rep = M;
        if (type == 1) {
            int nm = enc(imod(-a, q), imod(-b, q), imod(-c, q), imod(-e, q), q);
            if (nm < rep) rep = nm;
        } else if (type == 2) {
            for (int lam = 2; lam < q; lam++) {
                int nm = enc(imod(lam * a, q), imod(lam * b, q), imod(lam * c, q), imod(lam * e, q), q);
                if (nm < rep) rep = nm;
            }
        }
        rep_of[M] = rep;
    }
    int N = 0;
    for (int M = 0; M < Q4; M++) {
        if (rep_of[M] != M) continue;
        if (N >= MAXG) return 0;
        idx_of[M] = N;
        ea[N] = M / (q * q * q);
        eb[N] = (M / (q * q)) % q;
        ec[N] = (M / q) % q;
        ee[N] = M % q;
        N++;
    }
    gN = N;
    gid = idx_of[rep_of[enc(1, 0, 0, 1, q)]];
    if (gid < 0) return 0;
    for (int i = 0; i < N; i++) {
        int a = ea[i], b = eb[i], c = ec[i], e = ee[i];
        for (int j = 0; j < N; j++) {
            int p = ea[j], r = eb[j], s = ec[j], t = ee[j];
            int P00 = (a * p + b * s) % q, P01 = (a * r + b * t) % q;
            int P10 = (c * p + e * s) % q, P11 = (c * r + e * t) % q;
            int rr = rep_of[enc(P00, P01, P10, P11, q)];
            if (rr < 0) return 0;
            int id = idx_of[rr];
            if (id < 0) return 0;
            mt[i][j] = (unsigned short)id;
        }
    }
    for (int i = 0; i < N; i++) {
        int found = 0;
        for (int j = 0; j < N && !found; j++)
            if ((int)mt[i][j] == gid) { inv_[i] = j; found = 1; }
        if (!found) return 0;
    }
    return N;
}

/* ---- Haar (bi-Cayley) graph: a_x ~ b_{x s}, s in S. ---- */

static int S_[MAXD];
static int vis[MAXV], dep[MAXV], qu[MAXV];
static int vstamp = 0;

static int inS(int g) {
    for (int k = 0; k < d; k++)
        if (S_[k] == g) return 1;
    return 0;
}

/* Unreached (vertex, source) pairs within D from a_e and from b_e. Exact diameter test. */
static long eval_bad(void) {
    int N = gN, nv = 2 * N;
    long bad = 0;
    for (int si = 0; si < 2; si++) {
        int src = (si == 0) ? gid : N + gid;
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        dep[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++];
            int dv = dep[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + mt[v][S_[k]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; dep[u] = dv + 1; qu[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = mt[y][inv_[S_[k]]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; dep[u] = dv + 1; qu[tail++] = u; }
                }
            }
        }
        bad += nv - tail;
    }
    return bad;
}

static long anneal(int maxit, double until) {
    for (int k = 0; k < d; k++) {
        int g, dup;
        do {
            g = rndint(gN);
            dup = 0;
            for (int j = 0; j < k; j++)
                if (S_[j] == g) dup = 1;
        } while (dup);
        S_[k] = g;
    }
    long cur = eval_bad();
    double T = 2.0;
    for (int it = 0; it < maxit && cur > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        int k = rndint(d);
        int old = S_[k];
        int g;
        do { g = rndint(gN); } while (inS(g));
        S_[k] = g;
        long nb = eval_bad();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else S_[k] = old;
        T *= 0.9995;
        if (T < 0.1) T = 2.0;
    }
    return cur;
}

static void build_haar(Graph *g) {
    int N = gN;
    g->n = 2 * N;
    for (int v = 0; v < 2 * N; v++) { g->deg[v] = 0; g->side[v] = (v >= N); }
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            add_edge(g, x, N + mt[x][S_[k]]);
}

typedef struct { int type, q, N; } Cand;
static Cand cands[64];
static int ncand;

static void make_cands(long min_n) {
    static const int qs[7] = {2, 3, 5, 7, 11, 13, 17};
    ncand = 0;
    for (int qi = 0; qi < 7; qi++) {
        for (int type = 0; type < 3; type++) {
            int q = qs[qi];
            long ord = (long)q * (q * q - 1);
            if (type == 1 && q > 2) ord /= 2;
            if (ord <= d || 2 * ord > MOORE || 2 * ord > MAXV || ord > MAXG) continue;
            if (2 * ord < min_n) continue;
            cands[ncand].type = type;
            cands[ncand].q = q;
            cands[ncand].N = (int)ord;
            ncand++;
        }
    }
    for (int i = 1; i < ncand; i++) {
        Cand c = cands[i];
        int j = i - 1;
        while (j >= 0 && cands[j].N > c.N) { cands[j + 1] = cands[j]; j--; }
        cands[j + 1] = c;
    }
}

/* Ascending order of group order; each candidate gets an equal share of the remaining time.
 * A success is kept, and larger groups are still tried afterwards. */
static void search(Graph *best) {
    static Graph cand;
    long min_n = best->n + 1;
    if (target_n > min_n) min_n = target_n;
    make_cands(min_n);
    for (int ci = 0; ci < ncand; ci++) {
        double rem = t_end - now();
        if (rem < 0.2) break;
        double slice_end = now() + rem / (ncand - ci);
        if (!build_linear(cands[ci].type, cands[ci].q)) continue;
        if (gN != cands[ci].N || gN <= d) continue;
        while (now() < slice_end) {
            long bad = anneal(20000, slice_end);
            if (bad == 0) {
                build_haar(&cand);
                if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
                break;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + budget * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    best.n = 0;
    MOORE = moore_bound();
    if (d >= 2 && d <= MAXD - 1 && D >= 2) {
        read_start(&best);
        if (best.n < MOORE) search(&best);
    }
    if (best.n > 0) print_graph(&best);
    else printf("0 0\n");
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
    """Algebraic candidates valid for diameter D (may be empty)."""
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    target = RECORDS.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), target],
                         stdin_graph=best, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
