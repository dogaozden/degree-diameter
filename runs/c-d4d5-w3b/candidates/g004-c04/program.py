"""Group-lift engine. Python supplies a pool of finite groups (semidirect products and random
subgroups of block-symmetric permutation groups, none of them restricted to cyclic or metacyclic
form). C searches voltage lifts over these groups with simulated annealing on the orbit-reduced
diameter defect, then verifies every accepted lift with a full all-pairs BFS. The best algebraic
start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) is the fallback, and every returned graph is
checked with lib.is_valid."""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Voltage-lift search over arbitrary finite groups given as multiplication tables.
 * Usage:   prog d D seed budget min_n   < stdin
 * stdin:   header "G m" then 2m integers: flat tokens [N1, table1 (N1*N1 ints), N2, table2, ...].
 *          Table entry T[x*N+y] = x*y, identity at index 0.
 * stdout:  "n m" then m lines "u v" for the best valid lift with n > min_n, else "0 0".
 * A lift of base multigraph on p+p vertices with d-regular darts is a bipartite graph of order 2pN.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXP 4
#define MAXDART (MAXD * MAXP)
#define MAXV 2048
#define MAXN 256
#define MAXG 512

typedef struct { int i, j, g; } Dart;

static int d, D;
static int moore_cap;
static double t_stop;
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

static int ng;
static int gN[MAXG];
static int *gT[MAXG];

static int nv;
static int deg[MAXV];
static int adj[MAXV][MAXD];
static int dist[MAXV], que[MAXV];

/* A-fibre i, element x -> i*N + x ; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins A_{i,x} to B_{j, x*g} for every x. */
static void build_lift(int p, int N, const int *T, const Dart *dt, int nd) {
    nv = 2 * p * N;
    for (int v = 0; v < nv; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dt[t].i * N + x;
            int b = (p + dt[t].j) * N + T[x * N + dt[t].g];
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
}

/* Orbit-reduced defect: BFS from the 2p fibre representatives (element 0 of each fibre).
 * Left multiplication is an automorphism, so this equals the full defect being zero. */
static long orbit_bad(int p, int N) {
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[src] = 0;
        que[t++] = src;
        while (h < t) {
            int v = que[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    que[t++] = u;
                }
            }
        }
        total += nv - t;
    }
    return total;
}

/* Full verification: simple graph, bipartite, d-regular, all pairs within distance D. */
static int full_valid(int p, int N) {
    int half = p * N;
    for (int v = 0; v < nv; v++) {
        if (deg[v] != d) return 0;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if ((v < half) == (u < half)) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < nv; s++) {
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s] = 0;
        que[t++] = s;
        while (h < t) {
            int v = que[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    que[t++] = u;
                }
            }
        }
        if (t != nv) return 0;
    }
    return 1;
}

/* Random d-regular bipartite multigraph on p+p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP], st[2 * MAXP], top = 0, ns = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p] > 0)
                                   : (u < p && M[u][v - p] > 0);
                if (linked) {
                    seen[u] = 1;
                    ns++;
                    st[top++] = u;
                }
            }
        }
        if (ns == 2 * p) return;
    }
}

/* A voltage not already used by another dart on the same (i, j) block. */
static int fresh_g(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

/* Simulated annealing over the voltages of one random base. Returns 1 with a consistent
 * adjacency structure (built from dt) when the orbit defect reaches zero. */
static int try_lift(int p, int N, const int *T, long steps, double until,
                    Dart *dt, int *ndo) {
    int M[MAXP][MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_g(dt, nd, -1, i, j, N);
                nd++;
            }
    *ndo = nd;
    build_lift(p, N, T, dt, nd);
    long bad = orbit_bad(p, N);
    double temp = 1.0;
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_g(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(p, N, T, dt, nd);
        long nb = orbit_bad(p, N);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / temp))
            bad = nb;
        else
            dt[t].g = old;
        temp *= 0.9995;
        if (temp < 0.05) temp = 1.0;
    }
    return bad == 0;
}

static int read_groups(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || m < 0) return 0;
    long cnt = 2L * m;
    int *flat = malloc(sizeof(int) * (size_t)(cnt + 1));
    if (!flat) return 0;
    for (long k = 0; k < cnt; k++)
        if (scanf("%d", &flat[k]) != 1) {
            free(flat);
            return 0;
        }
    long pos = 0;
    for (int g = 0; g < n && ng < MAXG; g++) {
        if (pos >= cnt) break;
        int N = flat[pos++];
        if (N < 1 || N > MAXN || pos + (long)N * N > cnt) break;
        int *T = malloc(sizeof(int) * (size_t)N * N);
        memcpy(T, flat + pos, sizeof(int) * (size_t)N * N);
        pos += (long)N * N;
        int ok = 1;
        for (int x = 0; x < N && ok; x++)
            if (T[x] != x || T[x * N] != x) ok = 0;
        if (!ok) {
            free(T);
            continue;
        }
        gN[ng] = N;
        gT[ng] = T;
        ng++;
    }
    free(flat);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget min_n < groups\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    long minn = atol(argv[5]);
    double t0 = now();
    t_stop = t0 + budget * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_groups();
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        if (s > MAXV) break;
        pw *= (d - 1);
    }
    long mo = 2 * s;
    if (mo > MAXV) mo = MAXV;
    moore_cap = (int)mo;

    long bestn = minn;
    int found = 0, bp = 0, bN = 0, bg = 0, bnd = 0;
    static Dart best_dt[MAXDART], dt[MAXDART];
    static int cp[4 * MAXG], cg[4 * MAXG];

    while (now() < t_stop) {
        int nc = 0;
        for (int p = 1; p <= MAXP; p++)
            for (int g = 0; g < ng; g++) {
                long n2 = 2L * p * gN[g];
                if (n2 > bestn && n2 <= moore_cap && gN[g] >= d) {
                    cp[nc] = p;
                    cg[nc] = g;
                    nc++;
                }
            }
        if (nc == 0) break;
        int c = rndint(nc);
        int p = cp[c], g = cg[c], N = gN[g];
        double until = now() + 2.0;
        if (until > t_stop) until = t_stop;
        int nd = 0;
        if (try_lift(p, N, gT[g], 40000, until, dt, &nd)) {
            build_lift(p, N, gT[g], dt, nd);
            if (full_valid(p, N) && nv > bestn) {
                bestn = nv;
                found = 1;
                bp = p;
                bN = N;
                bg = g;
                bnd = nd;
                memcpy(best_dt, dt, sizeof(Dart) * (size_t)nd);
            }
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    build_lift(bp, bN, gT[bg], best_dt, bnd);
    long m = 0;
    for (int u = 0; u < nv; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adj[u][i]) m++;
    printf("%d %ld\n", nv, m);
    for (int u = 0; u < nv; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adj[u][i]) printf("%d %d\n", u, adj[u][i]);
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


# Block shapes for random subgroups of direct products of symmetric groups.
_BLOCKS = [(4, 4), (5, 3), (3, 3, 3), (4, 3), (6,), (5, 4), (2, 2, 2, 2, 2),
           (3, 3, 2), (7,), (4, 2, 2)]


def _rand_elem(blocks, rng):
    out = []
    off = 0
    for b in blocks:
        perm = list(range(b))
        rng.shuffle(perm)
        out.extend(off + x for x in perm)
        off += b
    return tuple(out)


def _perm_closure(gens, cap):
    """Subgroup generated by permutation tuples gens, as (elements, index); None if it exceeds cap.
    Element 0 is the identity."""
    k = len(gens[0])
    e = tuple(range(k))
    elems = [e]
    index = {e: 0}
    stack = [e]
    while stack:
        x = stack.pop()
        for g in gens:
            y = tuple(x[i] for i in g)
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
                stack.append(y)
    return elems, index


def _perm_table(elems, index):
    N = len(elems)
    flat = []
    for a in elems:
        for b in elems:
            flat.append(index[tuple(a[i] for i in b)])
    return N, flat


def _elem_order(x, e):
    c, y = 1, x
    while y != e:
        y = tuple(x[i] for i in y)
        c += 1
    return c


def _make_pool(lo, hi, rng, deadline, want):
    """Pool of (N, flat table) groups with lo <= N <= hi. Half semidirect, half random subgroups."""
    pool, seen = [], set()
    sd = []
    for N in range(lo, hi + 1):
        for m in range(1, N + 1):
            if N % m:
                continue
            k = N // m
            for r in (range(1, m) if m > 1 else [0]):
                if m > 1 and math.gcd(r, m) != 1:
                    continue
                if pow(r, k, m) != 1 % m:
                    continue
                sd.append((m, k, r))
    rng.shuffle(sd)
    for m, k, r in sd[: want // 2]:
        if time.monotonic() > deadline:
            break
        try:
            N, mul, _ = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        if N < lo or N > hi:
            continue
        tab = [mul(x, y) for x in range(N) for y in range(N)]
        pool.append((N, tab))
    attempts = 0
    while len(pool) < want and attempts < 3000 and time.monotonic() < deadline:
        attempts += 1
        blocks = rng.choice(_BLOCKS)
        gens = [_rand_elem(blocks, rng) for _ in range(rng.choice((2, 2, 3)))]
        res = _perm_closure(gens, hi)
        if res is None:
            continue
        elems, index = res
        N = len(elems)
        if N < lo:
            continue
        sig = (N, tuple(sorted(_elem_order(x, elems[0]) for x in elems)))
        if sig in seen:
            continue
        seen.add(sig)
        pool.append(_perm_table(elems, index))
    return pool


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

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    try:
        rng = random.Random(seed * 1000003 + 17 * d + D)
        moore = lib.moore_bound(d, D)
        lo = max(d, (best[0] + 2) // 8)
        hi = min(256, max(lo, moore // 2))
        deadline = time.monotonic() + min(5.0, 0.1 * time_limit)
        pool = _make_pool(lo, hi, rng, deadline, 60)
        if not pool:
            return best

        budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.5
        if budget < 3.0:
            return best

        tokens = []
        for N, tab in pool:
            tokens.append(N)
            tokens.extend(tab)
        if len(tokens) % 2:
            tokens.append(0)
        pairs = [(tokens[i], tokens[i + 1]) for i in range(0, len(tokens), 2)]

        text = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0]],
                         stdin_graph=(len(pool), pairs), timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
