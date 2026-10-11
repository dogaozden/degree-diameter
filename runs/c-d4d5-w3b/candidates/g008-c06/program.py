"""Bi-Cayley search over many small groups (new construction route).

Python builds a pool of groups of order N (cyclic, semidirect Z_m x| Z_k, direct products of small
groups, and random permutation groups) with orders in the window that could beat the current start.
Each group is passed to the C engine as a multiplication table. For a connection set S of size d,
the bi-Cayley graph has vertices A_g, B_g (g in G) and edges A_g - B_{g s} (s in S). Left translation
acts transitively on each side, so the diameter is at most D iff BFS from A_e and from B_e reach every
vertex within D steps. C runs simulated annealing over S for every group in round-robin order.

The group tables are packed into the stdin "graph" slot as integers (lib.run_c only accepts a graph),
so C reads "n m" and then 2m integers in a fixed layout.
Python still validates the final answer with lib.is_valid and falls back to the algebraic start.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley annealing over many groups.
 * Usage: prog d D seed time_limit min_n < packed
 * packed: "n m" then 2m integers: G, then for each group N followed by its N*N table
 * (row-major, identity element 0, T[x*N+y] = x*y).
 * Output: best graph with more than min_n vertices, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 256
#define MAXV (2 * MAXN)
#define MAXD 64
#define STEPS 3000

typedef struct {
    int N;
    unsigned short *T;
    int inv[MAXN];
} Grp;

static int d, D;
static Grp *grp = NULL;
static int ng = 0;
static int dist_[MAXV], que[MAXV];
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

static int contains(const int *S, int k, int x) {
    for (int i = 0; i < k; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Number of vertices reached from src within D steps (src included). */
static int bfs_reach(const Grp *G, const int *S, const int *iS, int src) {
    int N = G->N, V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    que[tail++] = src;
    while (head < tail) {
        int v = que[head++];
        if (dist_[v] >= D) continue;
        int nd = dist_[v] + 1;
        if (v < N) {
            const unsigned short *row = G->T + (size_t)v * N;
            for (int j = 0; j < d; j++) {
                int u = N + row[S[j]];
                if (dist_[u] < 0) {
                    dist_[u] = nd;
                    que[tail++] = u;
                }
            }
        } else {
            int h = v - N;
            const unsigned short *row = G->T + (size_t)h * N;
            for (int j = 0; j < d; j++) {
                int u = row[iS[j]];
                if (dist_[u] < 0) {
                    dist_[u] = nd;
                    que[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Zero iff the bi-Cayley graph of S has diameter <= D. */
static int cost(const Grp *G, const int *S, const int *iS) {
    int V = 2 * G->N;
    return (V - bfs_reach(G, S, iS, 0)) + (V - bfs_reach(G, S, iS, G->N));
}

static int best_n = 0, best_gi = -1;
static int best_S[MAXD];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit min_n < packed\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int minn = atoi(argv[5]);
    double t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || m < 0) { printf("0 0\n"); return 0; }
    long cnt = 2L * m;
    int *a = malloc(sizeof(int) * (size_t)(cnt + 2));
    long got = 0;
    for (long i = 0; i < cnt; i++) {
        if (scanf("%d", &a[i]) != 1) break;
        got++;
    }
    long pos = 0;
    int G = got > 0 ? a[pos++] : 0;
    if (G < 0) G = 0;
    grp = malloc(sizeof(Grp) * (size_t)(G > 0 ? G : 1));
    for (int gi = 0; gi < G && pos < got; gi++) {
        int N = a[pos++];
        if (N < 1 || N > MAXN || pos + (long)N * N > got) break;
        int *tab = a + pos;
        pos += (long)N * N;
        int ok = 1;
        for (long i = 0; i < (long)N * N && ok; i++)
            if (tab[i] < 0 || tab[i] >= N) ok = 0;
        for (int y = 0; y < N && ok; y++)
            if (tab[y] != y || tab[y * N] != y) ok = 0;
        if (!ok) continue;
        Grp *Gr = &grp[ng];
        Gr->N = N;
        Gr->T = malloc(sizeof(unsigned short) * (size_t)N * N);
        for (long i = 0; i < (long)N * N; i++) Gr->T[i] = (unsigned short)tab[i];
        for (int x = 0; x < N && ok; x++) {
            int found = -1;
            for (int y = 0; y < N; y++)
                if (Gr->T[x * N + y] == 0) { found = y; break; }
            if (found < 0) ok = 0;
            else Gr->inv[x] = found;
        }
        if (!ok) { free(Gr->T); continue; }
        ng++;
    }
    free(a);

    best_n = minn;
    int S[MAXD], iS[MAXD];
    while (now() < t_end) {
        int progressed = 0;
        for (int gi = 0; gi < ng && now() < t_end; gi++) {
            Grp *Gr = &grp[gi];
            if (Gr->N < d) continue;
            if (2 * Gr->N <= best_n) continue;
            progressed = 1;
            for (int j = 0; j < d; j++) {
                int x;
                do { x = rndint(Gr->N); } while (contains(S, j, x));
                S[j] = x;
                iS[j] = Gr->inv[x];
            }
            int cur = cost(Gr, S, iS);
            for (int s = 0; s < STEPS && cur > 0; s++) {
                if ((s & 255) == 0 && now() > t_end) break;
                int j = rndint(d);
                int x = rndint(Gr->N);
                if (contains(S, d, x)) continue;
                int old = S[j];
                S[j] = x;
                iS[j] = Gr->inv[x];
                int c = cost(Gr, S, iS);
                double T = 1.5 * (1.0 - (double)s / STEPS) + 0.05;
                if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) {
                    cur = c;
                } else {
                    S[j] = old;
                    iS[j] = Gr->inv[old];
                }
            }
            if (cur == 0) {
                best_n = 2 * Gr->N;
                best_gi = gi;
                memcpy(best_S, S, sizeof(int) * (size_t)d);
            }
        }
        if (!progressed) break;
    }

    if (best_gi < 0) { printf("0 0\n"); return 0; }
    Grp *Gr = &grp[best_gi];
    int N = Gr->N;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, N + (int)Gr->T[g * N + best_S[j]]);
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


# ------------------------------------------------------------ group pool

def _table(N, mul):
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _cyclic_table(N):
    return _table(N, lambda x, y: (x + y) % N)


def _semidirect_tables(N, limit=2):
    out = []
    for m in range(3, N + 1):
        if N % m:
            continue
        k = N // m
        count = 0
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m:
                continue
            try:
                _, mul, _ = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            out.append(_table(N, mul))
            count += 1
            if count >= limit:
                break
    return out


def _product_table(T1, N1, T2, N2):
    N = N1 * N2
    T = [[0] * N for _ in range(N)]
    for x in range(N):
        a1, b1 = divmod(x, N2)
        for y in range(N):
            a2, b2 = divmod(y, N2)
            T[x][y] = T1[a1][a2] * N2 + T2[b1][b2]
    return T


def _perm_group(rng, t, hi):
    """Random 2-generated permutation group on t points; None if its order exceeds hi."""
    def comp(p, q):
        return tuple(p[i] for i in q)

    gens = []
    for _ in range(2):
        g = list(range(t))
        rng.shuffle(g)
        gens.append(tuple(g))
    ident = tuple(range(t))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for e in frontier:
            for g in gens:
                f = comp(e, g)
                if f not in index:
                    if len(elems) >= hi:
                        return None
                    index[f] = len(elems)
                    elems.append(f)
                    nxt.append(f)
        frontier = nxt
    N = len(elems)
    T = [[index[comp(elems[i], elems[j])] for j in range(N)] for i in range(N)]
    return N, T


def make_groups(lo, hi, seed, deadline, cap):
    """Return a list of (N, table) with lo <= N <= hi, identity at index 0."""
    rng = random.Random(seed)
    groups = []
    if lo > hi:
        return groups
    for N in range(lo, hi + 1):
        if time.monotonic() > deadline or len(groups) >= cap:
            break
        groups.append((N, _cyclic_table(N)))
        for T in _semidirect_tables(N):
            groups.append((N, T))

    tries = 0
    while time.monotonic() < deadline and len(groups) < cap and tries < 3000:
        tries += 1
        res = _perm_group(rng, rng.randint(4, 8), hi)
        if res is not None and lo <= res[0] <= hi:
            groups.append(res)

    pool = []
    for N in range(2, 31):
        pool.append((N, _cyclic_table(N)))
        for T in _semidirect_tables(N, limit=1):
            pool.append((N, T))
    products = 0
    for N1, T1 in pool:
        for N2, T2 in pool:
            N = N1 * N2
            if N < lo or N > hi or products >= 40:
                continue
            if len(groups) >= cap or time.monotonic() > deadline:
                return groups
            groups.append((N, _product_table(T1, N1, T2, N2)))
            products += 1
    return groups


def _encode(groups):
    """Pack group tables into a graph-shaped stdin: "1 m" then 2m integers (lib.run_c format)."""
    flat = [len(groups)]
    for N, T in groups:
        flat.append(N)
        for row in T:
            flat.extend(row)
    if len(flat) % 2:
        flat.append(0)
    edges = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
    return (1, edges)


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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 1.0:
        return best

    lo = max(d, best[0] // 2 + 1)
    hi = min(moore // 2, 256)  # |A| = N, total 2N vertices
    if lo > hi:
        return best

    deadline = time.monotonic() + 0.25 * budget
    try:
        groups = make_groups(lo, hi, seed, deadline, cap=120)
    except Exception:
        groups = []
    if not groups:
        return best

    try:
        payload = _encode(groups)
        c_budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
        if c_budget <= 0.5:
            return best
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget * 0.9:.2f}", best[0]],
                         stdin_graph=payload, timeout=c_budget + 3)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
