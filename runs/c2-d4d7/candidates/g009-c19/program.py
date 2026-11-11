"""Bi-Cayley / voltage-lift search by simulated annealing over dart voltages (targets d=4, D=7).

Change from the parent: the lift search is replaced. The parent hill-climbed with random restarts over
semidirect groups Z_m x|_r Z_k. This version draws a random base multigraph on P <= 3 vertices per side,
then anneals only the voltages with a Metropolis rule. The cost is the number of (fibre representative,
vertex) pairs at distance > D, computed by BFS from the 2P fibre representatives only. Left
multiplication by the group is an automorphism, so this count is zero exactly when the lift has
diameter <= D. Each candidate that reaches zero is re-verified by a full BFS from every vertex on
explicit adjacency lists, and only then recorded. The C engine outputs the largest verified lift, or
"0 0". Python keeps its algebraic start graph unless the output is larger and passes lib.is_valid.
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

#define MAXH 2048
#define MAXV 4096
#define MAXD 32
#define MAXP 3
#define MOVES 15000

static int d, D;
static double t_end;
static int P, N;              /* P fibres per side, group order N */
static int gm, gk, gr;        /* group Z_gm x|_gr Z_gk, N = gm*gk, element a*gk+b */
static int rp[MAXH];          /* rp[b] = gr^b mod gm */
static int nd;                /* darts = d*P */
static int di[MAXD * MAXP], dj[MAXD * MAXP], dg[MAXD * MAXP];
static int deg[MAXV];
static int adj[MAXV][MAXD];
static int dist[MAXV], qu[MAXV];

static int bestV = 0;
static int bP, bN, bgm, bgk, bgr, bnd;
static int bdi[MAXD * MAXP], bdj[MAXD * MAXP], bdg[MAXD * MAXP];

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

static void set_rp(void) {
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
}

/* Element (a,b) * (c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

/* Uniform choice among all semidirect groups of order n (reservoir sampling). */
static int pick_group(int n) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { gm = m; gk = k; gr = r; found = 1; }
        }
    }
    if (!found) return 0;
    set_rp();
    return 1;
}

static int find(int *par, int x) {
    while (par[x] != x) x = par[x];
    return x;
}

/* Random d-regular base multigraph on P + P vertices (sum of d permutations), connected. */
static void make_base(void) {
    for (;;) {
        nd = 0;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < P; i++) {
                di[nd] = i; dj[nd] = perm[i]; dg[nd] = 0; nd++;
            }
        }
        int par[2 * MAXP];
        for (int v = 0; v < 2 * P; v++) par[v] = v;
        for (int t = 0; t < nd; t++) {
            int a = find(par, di[t]), b = find(par, P + dj[t]);
            par[a] = b;
        }
        int root = find(par, 0), ok = 1;
        for (int v = 1; v < 2 * P; v++)
            if (find(par, v) != root) { ok = 0; break; }
        if (ok) return;
    }
}

/* A voltage for dart t that is not already used by a parallel dart. */
static int fresh(int t) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int s = 0; s < nd; s++)
            if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) { ok = 0; break; }
        if (ok) return g;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (P+j)*N + x.
 * Dart (i,j,g) joins A(i,x) to B(j, x*g) for every x. */
static void build_lift(void) {
    int V = 2 * P * N;
    for (int v = 0; v < V; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++) {
        int ba = di[t] * N, bb = (P + dj[t]) * N;
        for (int x = 0; x < N; x++) {
            int a = ba + x, b = bb + gmul(x, dg[t]);
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
    }
}

/* Number of vertices at distance > D from src. */
static long bfs_unreached(int src, int V) {
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        if (dist[v] >= D) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                qu[tail++] = u;
            }
        }
    }
    return (long)(V - tail);
}

/* Orbit-reduced cost: BFS from the 2P fibre representatives (element 0 of each fibre). */
static long cost_eval(void) {
    build_lift();
    int V = 2 * P * N;
    long c = 0;
    for (int f = 0; f < 2 * P; f++) c += bfs_unreached(f * N, V);
    return c;
}

/* Metropolis annealing over the voltages of the current base. Returns 1 if cost 0 is reached. */
static int anneal(double until, long moves) {
    for (int t = 0; t < nd; t++) dg[t] = 0;
    for (int t = 0; t < nd; t++) dg[t] = fresh(t);
    long cur = cost_eval();
    if (cur == 0) return 1;
    for (long it = 0; it < moves; it++) {
        if ((it & 127) == 0 && now() > until) break;
        double T = 1.5 * (1.0 - (double)it / (double)moves) + 0.05;
        int t = rndint(nd);
        int old = dg[t];
        dg[t] = fresh(t);
        long nc = cost_eval();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            dg[t] = old;
        }
    }
    return 0;
}

/* Full independent check: explicit adjacency, every vertex degree d, BFS from every vertex. */
static int verify_full(void) {
    build_lift();
    int V = 2 * P * N;
    for (int v = 0; v < V; v++) {
        if (deg[v] != d) return 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < i; j++)
                if (adj[v][i] == adj[v][j]) return 0;
    }
    for (int s = 0; s < V; s++)
        if (bfs_unreached(s, V) != 0) return 0;
    return 1;
}

static void save_best(void) {
    bP = P; bN = N; bgm = gm; bgk = gk; bgr = gr; bnd = nd;
    memcpy(bdi, di, sizeof(int) * nd);
    memcpy(bdj, dj, sizeof(int) * nd);
    memcpy(bdg, dg, sizeof(int) * nd);
    bestV = 2 * P * N;
}

static void print_best(void) {
    P = bP; N = bN; gm = bgm; gk = bgk; gr = bgr; nd = bnd;
    memcpy(di, bdi, sizeof(int) * nd);
    memcpy(dj, bdj, sizeof(int) * nd);
    memcpy(dg, bdg, sizeof(int) * nd);
    set_rp();
    printf("%d %ld\n", 2 * P * N, (long)nd * N);
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", di[t] * N + x, (P + dj[t]) * N + gmul(x, dg[t]));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    bestV = n0 > 0 ? n0 : 0;

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    long moore = moore_bound();
    int found = 0;
    int skips = 0;
    while (now() < t_end && skips < 100000) {
        P = 1 + rndint(MAXP);
        long Nlo = bestV / (2 * P) + 1;
        if (Nlo < 2 * d) Nlo = 2 * d;
        long Nt = Nlo + rndint(4);
        if (2L * P * Nt > moore || 2L * P * Nt > MAXV || Nt > MAXH) { skips++; continue; }
        N = (int)Nt;
        if (!pick_group(N)) { skips++; continue; }
        skips = 0;
        make_base();
        if (anneal(t_end, MOVES) && verify_full()) {
            save_best();
            found = 1;
        }
    }
    if (!found) { printf("0 0\n"); return 0; }
    print_best();
    return 0;
}
'''


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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 32 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
