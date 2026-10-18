"""Non-metacyclic bi-Cayley search over PSL(2,q) and PGL(2,q).

Construction: a bipartite lift with P fibres per side (P in {1, 2}) over a finite group G, with
d random base darts. Dart (i, j, g) joins (A, i, x) to (B, j, x*g). Left multiplication is an
automorphism that acts regularly on each fibre, so the diameter check needs one BFS per fibre.

Groups come from permutation generators, closed in C into a multiplication table:
- PGL(2,q) and PSL(2,q) for primes q, which are non-solvable and not metacyclic, so they differ
  from the metacyclic lifts of the parent.
- Cyclic groups as a last resort, so the search still has an abelian option.

Each candidate (group, P) is searched by simulated annealing on voltages, then coordinate
polish. Candidates run in increasing vertex count, and the largest valid graph wins. Python
builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) as a fallback,
and only accepts C output that is valid by lib.is_valid and strictly larger.
"""
import time
import itertools

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
#define MAXP 2
#define MAXDART (MAXD * MAXP)
#define MAXG 3300
#define MAXK 72
#define HSZ 16384

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D, P_FIX;
static long MOORE;
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
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------- finite groups as multiplication tables ---------- */

static int G_N = 0, G_k = 0;
static unsigned char G_el[MAXG][MAXK];
static int htab[HSZ];
static uint16_t MT[MAXG][MAXG];
static int gen[4][MAXK];
static int ngen = 0;

static int is_prime(int q) {
    if (q < 2) return 0;
    for (int r = 2; r * r <= q; r++)
        if (q % r == 0) return 0;
    return 1;
}

static int primroot(int q) {
    for (int g = 2; g < q; g++) {
        int x = g, ord = 1;
        while (x != 1) { x = (int)((long)x * g % q); ord++; }
        if (ord == q - 1) return g;
    }
    return 1;
}

static unsigned hash_perm(const unsigned char *p) {
    unsigned h = 2166136261u;
    for (int i = 0; i < G_k; i++) { h ^= p[i]; h *= 16777619u; }
    return h & (HSZ - 1);
}

static int find_perm(const unsigned char *p) {
    unsigned h = hash_perm(p);
    for (;;) {
        int e = htab[h];
        if (e == 0) return -1;
        if (memcmp(G_el[e - 1], p, G_k) == 0) return e - 1;
        h = (h + 1) & (HSZ - 1);
    }
}

static int insert_perm(const unsigned char *p) {
    if (G_N >= MAXG) return -1;
    memcpy(G_el[G_N], p, G_k);
    unsigned h = hash_perm(p);
    while (htab[h]) h = (h + 1) & (HSZ - 1);
    htab[h] = G_N + 1;
    return G_N++;
}

/* type 0: PGL(2,q), type 1: PSL(2,q), type 2: unused, type 3: cyclic Z_q.
 * Projective line points are 0..q-1 and infinity = q. */
static int build_group(int type, int q) {
    if (type == 3) {
        if (q < 2 || q > MAXG) return 0;
        G_N = q;
        for (int x = 0; x < q; x++)
            for (int y = 0; y < q; y++)
                MT[x][y] = (uint16_t)((x + y) % q);
        return 1;
    }
    if (q < 3 || q > 61 || !is_prime(q)) return 0;
    int k = q + 1;
    G_k = k;
    int g = primroot(q);
    for (int i = 0; i < q; i++) gen[0][i] = (i + 1) % q;   /* x -> x+1 */
    gen[0][q] = q;
    if (type == 0) {
        for (int i = 0; i < q; i++) gen[1][i] = (int)((long)g * i % q);   /* x -> g x */
        gen[1][q] = q;
        gen[2][0] = q;
        gen[2][q] = 0;
        for (int i = 1; i < q; i++) gen[2][i] = (int)powmod(i, q - 2, q); /* x -> 1/x */
    } else {
        int g2 = (int)((long)g * g % q);
        for (int i = 0; i < q; i++) gen[1][i] = (int)((long)g2 * i % q);  /* x -> g^2 x */
        gen[1][q] = q;
        gen[2][0] = q;
        gen[2][q] = 0;
        for (int i = 1; i < q; i++)
            gen[2][i] = (q - (int)powmod(i, q - 2, q)) % q;               /* x -> -1/x */
    }
    ngen = 3;

    unsigned char id[MAXK];
    memset(htab, 0, sizeof htab);
    G_N = 0;
    for (int i = 0; i < k; i++) id[i] = (unsigned char)i;
    insert_perm(id);
    for (int h = 0; h < G_N; h++) {
        for (int s = 0; s < ngen; s++) {
            unsigned char c[MAXK];
            for (int i = 0; i < k; i++) c[i] = G_el[h][gen[s][i]];
            if (find_perm(c) < 0 && insert_perm(c) < 0) return 0;
        }
    }
    for (int x = 0; x < G_N; x++)
        for (int y = 0; y < G_N; y++) {
            unsigned char c[MAXK];
            for (int i = 0; i < k; i++) c[i] = G_el[x][G_el[y][i]];
            int z = find_perm(c);
            if (z < 0) return 0;
            MT[x][y] = (uint16_t)z;
        }
    return 1;
}

/* ---------- lift, darts, and annealing ---------- */

static int di[MAXDART], dj[MAXDART], dg[MAXDART];
static int nd = 0;

static void make_darts(void) {
    nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < P_FIX; i++) perm[i] = i;
        for (int i = P_FIX - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < P_FIX; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

static int clashes(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

/* A-fibre i element x -> i*N + x; B-fibre j element x -> (P+j)*N + x. */
static void build_lift(Graph *g) {
    int N = G_N, S = P_FIX * N;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, S + dj[t] * N + MT[x][dg[t]]);
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Sum over the 2P fibre identities of vertices not reached within D steps. */
static long orbit_bad(const Graph *g) {
    int nv = g->n, N = G_N;
    long total = 0;
    for (int b = 0; b < 2 * P_FIX; b++) {
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

static long anneal(Graph *g, int maxit, double until) {
    static int bestdg[MAXDART];
    int N = G_N;
    build_lift(g);
    long bad = orbit_bad(g);
    long bestbad = bad;
    memcpy(bestdg, dg, sizeof(int) * nd);
    double T = 1.0;
    for (int it = 0; it < maxit && bestbad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng)) continue;
        dg[t] = ng;
        int t2 = -1, old2 = 0;
        if (rndint(4) == 0) {
            t2 = rndint(nd);
            if (t2 == t) t2 = -1;
        }
        if (t2 >= 0) {
            old2 = dg[t2];
            int ng2 = rndint(N);
            if (ng2 == old2 || clashes(t2, ng2)) { dg[t] = old; continue; }
            dg[t2] = ng2;
        }
        build_lift(g);
        long nb = orbit_bad(g);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestbad) {
                bestbad = bad;
                memcpy(bestdg, dg, sizeof(int) * nd);
            }
        } else {
            dg[t] = old;
            if (t2 >= 0) dg[t2] = old2;
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    memcpy(dg, bestdg, sizeof(int) * nd);
    build_lift(g);
    return bestbad;
}

static long polish(Graph *g, long bad, double until) {
    int N = G_N;
    for (int sweep = 0; sweep < 3 && bad > 0; sweep++) {
        int improved = 0;
        for (int t = 0; t < nd && bad > 0; t++) {
            if (now() > until) break;
            int old = dg[t], bestg = old;
            long bestb = bad;
            for (int k = 0; k < 40; k++) {
                int ng = rndint(N);
                if (ng == old || clashes(t, ng)) continue;
                dg[t] = ng;
                build_lift(g);
                long nb = orbit_bad(g);
                if (nb < bestb) { bestb = nb; bestg = ng; }
            }
            dg[t] = bestg;
            build_lift(g);
            bad = orbit_bad(g);
            if (bestg != old) improved = 1;
        }
        if (!improved) break;
    }
    build_lift(g);
    return bad;
}

/* Random restarts of anneal + polish for the fixed group until the slice ends. */
static void search(Graph *best, double until) {
    static Graph cand;
    int N = G_N;
    while (now() < until) {
        make_darts();
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g));
            dg[t] = g;
        }
        long bad = anneal(&cand, 6000, until);
        if (bad > 0) bad = polish(&cand, bad, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return;
        }
    }
}

/* argv: d D seed time_limit type q P; the start graph comes on stdin. */
int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: %s d D seed time_limit type q P < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int type = atoi(argv[5]);
    int q = atoi(argv[6]);
    P_FIX = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && P_FIX >= 1 && P_FIX <= MAXP && best.n < MOORE) {
        if (build_group(type, q) && G_N >= d &&
            2L * P_FIX * G_N <= MOORE && 2L * P_FIX * G_N <= MAXN &&
            2L * P_FIX * G_N > best.n) {
            search(&best, t_end);
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

RECORDS = {(3, 3): 14, (4, 8): 2184}
MAX_GROUP = 3300     # largest multiplication table the C engine accepts
MAX_VERTS = 8192


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


def _is_prime(q):
    return q >= 2 and all(q % r for r in range(2, int(q ** 0.5) + 1))


def group_candidates(d, D, lo, moore):
    """(V, type, q, P) runs with lo <= V <= moore, in ascending V.
    Non-abelian PGL/PSL lifts come first; cyclic lifts are appended as a last resort."""
    main = []
    for q in range(3, 62):
        if not _is_prime(q):
            continue
        for typ, N in ((0, q * (q * q - 1)), (1, q * (q * q - 1) // 2)):
            if N < d or N > MAX_GROUP:
                continue
            for p in (1, 2):
                V = 2 * p * N
                if lo <= V <= moore and V <= MAX_VERTS:
                    main.append((V, typ, q, p))
    main.sort()
    cyc = []
    for p in (1, 2):
        N = -(-lo // (2 * p))
        V = 2 * p * N
        if d <= N <= MAX_GROUP and V <= moore and V <= MAX_VERTS:
            cyc.append((V, 3, N, p))
    cyc.sort()
    return main + cyc


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 2.0:
        return best
    deadline = time.monotonic() + budget

    lo = max(best[0] + 1, RECORDS.get((d, D), 0))
    cands = group_candidates(d, D, lo, moore)
    for idx, (V, typ, q, p) in enumerate(cands):
        if V <= best[0]:
            continue
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        share = min(remaining, max(2.0, remaining / (len(cands) - idx)))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(share, 2), typ, q, p],
                             stdin_graph=best, timeout=share + 3.0)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            continue
    return best
