"""Bi-Cayley lift search, driven by a C engine with a Python fallback.

Construction: vertices are A_{i,g} = i*G + g (i < k) and B_{p,h} = (k+p)*G + h with
G = |Z_m x| Z_k2|. Each of the d layers pairs A_i with B_{layers[l][i]} through a voltage s,
so every vertex has degree d.

Search change: the C engine now evaluates reachability on the block level. Left
multiplication by G is an automorphism of every lift, so all vertices in one block have the
same reach set (as a set of blocks). The engine therefore runs the distance recurrence on
the 2k blocks instead of all N vertices, and the unreached count is G times the block sum.
Each annealing move becomes roughly G times cheaper. Darts are written only when a valid
lift is recorded. Time is checked every 256 moves, not every move. The schedule is longer
to use the extra moves. Successive halving over random candidate lifts, the algebraic
baselines (projective planes, generalized quadrangles, K_{d,d}), and the slack extension are
unchanged. Every valid lift is checked with lib.is_valid before it is kept. Any C failure
falls back to the Python search.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define PENALTY 1000
#define POOL 12

typedef uint64_t u64;

static u64 rs;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { int v = (int)(rndu() * n); return v >= n ? n - 1 : v; }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long gcdll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

typedef struct { int m, k2, G; long long r; int pw[64]; } Group;
static Group grp;

static void set_group(int m, int k2, long long r) {
    grp.m = m; grp.k2 = k2; grp.G = m * k2; grp.r = r;
    long long p = 1 % m;
    for (int b = 0; b < k2; b++) { grp.pw[b] = (int)p; p = (p * r) % m; }
}

/* element a*k2+b, (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + (long long)grp.pw[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

/* inverse of (a,b) is (-r^(-b) a, -b) */
static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)grp.pw[nb] * a) % m;
    long long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

typedef struct {
    int m, k2, K, ord;
    long long r;
    int layers[MAXD][MAXK];
    int S[MAXD][MAXK];
    long long cost;
    double c0;
    long steps;
    long Tmax;
} Cand;

static int DEG, D_, K, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;     /* nbr[l*N + v], filled only when a solution is recorded */
static long capN = 0;
static u64 FULL;
static int blk_nb[MAXD][2 * MAXK];  /* block-level neighbour block of block x in layer l */
static u64 bra[2 * MAXK];           /* bra[x] = set of blocks within distance D of block x */

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

static void emit_best(void) {
    if (best_m == 0) {
        printf("0 0\n");
        return;
    }
    printf("%d %d\n", best_n, best_m);
    for (int j = 0; j < best_m; j++)
        printf("%d %d\n", best_e[2 * j], best_e[2 * j + 1]);
}

static void ensure_capacity(long n) {
    if (n <= capN) return;
    free(nbr);
    capN = n + n / 4 + 16;
    nbr = malloc(sizeof(int) * (size_t)DEG * (size_t)capN);
    if (!nbr) { emit_best(); exit(0); }
}

static int gmul_dummy_guard(void) { return 0; }

static void set_dart(int l, int i) {
    int p = layers[l][i], s = S[l][i];
    int sinv = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int q = K + p;
    for (int g = 0; g < G; g++) nl[i * G + g] = q * G + gmul(g, s);
    for (int h = 0; h < G; h++) nl[q * G + h] = i * G + gmul(h, sinv);
}

/* Block-level adjacency: A block i joins B block layers[l][i]; each B block has one partner per layer. */
static void build_blocks(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int q = K + layers[l][i];
            blk_nb[l][i] = q;
            blk_nb[l][q] = i;
        }
}

/* Reachability on blocks. Left multiplication is an automorphism, so each block has one reach set.
   Returns the exact number of unreached (vertex, block) pairs over all N vertices. */
static int reach_eval(void) {
    u64 cur[2 * MAXK], nxt[2 * MAXK];
    int NB = 2 * K;
    for (int x = 0; x < NB; x++) cur[x] = (u64)1 << x;
    for (int round = 0; round < D_; round++) {
        int changed = 0;
        for (int x = 0; x < NB; x++) {
            u64 u = cur[x];
            for (int l = 0; l < DEG; l++) u |= cur[blk_nb[l][x]];
            nxt[x] = u;
            if (u != cur[x]) changed = 1;
        }
        for (int x = 0; x < NB; x++) cur[x] = nxt[x];
        if (!changed) break;
    }
    int unr = 0;
    for (int x = 0; x < NB; x++) {
        bra[x] = cur[x];
        unr += pc64(FULL & ~cur[x]);
    }
    return unr * G;
}

static long long eval_cost(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) dup++;
    build_blocks();
    int unr = reach_eval();
    return (long long)unr + (long long)PENALTY * dup;
}

static void record_solution(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
    int m = K * G * DEG;
    int *e = malloc(sizeof(int) * 2 * (size_t)m);
    if (!e) return;
    int idx = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < DEG; l++) {
            e[2 * idx] = u;
            e[2 * idx + 1] = nbr[(size_t)l * N + u];
            idx++;
        }
    free(best_e);
    best_e = e;
    best_m = m;
    best_n = N;
}

/* Load candidate state into the globals and return its exact cost. */
static long long cand_load(const Cand *c) {
    set_group(c->m, c->k2, c->r);
    K = c->K;
    G = grp.G;
    N = 2 * K * G;
    FULL = (((u64)1) << (2 * K)) - 1;
    ensure_capacity(N);
    memcpy(layers, c->layers, sizeof(layers));
    memcpy(S, c->S, sizeof(S));
    return eval_cost();
}

static void cand_save(Cand *c) {
    memcpy(c->layers, layers, sizeof(layers));
    memcpy(c->S, S, sizeof(S));
}

/* Continue annealing from the current globals for up to `steps` moves.
   Temperature decays over the candidate's total schedule (step0 + t vs Tmax). */
static long long anneal_run(long long cost, double c0, long steps, long step0,
                            long Tmax, double deadline, long *done) {
    *done = 0;
    for (long t = 0; t < steps; t++) {
        if (cost == 0) break;
        if ((t & 255) == 0 && now() > deadline) break;
        (*done)++;
        long gt = step0 + t;
        double temp = 0.5;
        if (gt < Tmax) temp = 0.01 * c0 * (1.0 - (double)gt / (double)Tmax);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndu() < 0.25) {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            long long c2 = eval_cost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            }
            continue;
        }

        int l = -1, i = -1;
        if (rndu() < 0.4) {
            for (int tries = 0; tries < 30 && l < 0; tries++) {
                int v = rndint(N);
                int block = v / G;
                if ((bra[block] & FULL) != FULL) {
                    if (block < K) {
                        i = block;
                        l = rndint(DEG);
                    } else {
                        int ll = rndint(DEG);
                        for (int j = 0; j < K; j++)
                            if (layers[ll][j] == block - K) { i = j; l = ll; break; }
                    }
                }
            }
        }
        if (l < 0) { l = rndint(DEG); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        long long c2 = eval_cost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            S[l][i] = old;
        }
    }
    return cost;
}

static const int K2LIST[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, int *pm, int *pk2, long long *pr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2LIST[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = -1;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
        } else {
            if (m > 2) {
                for (int t = 0; t < 60; t++) {
                    long long c = 2 + rndint(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
                }
            } else {
                r = 1;
            }
            if (r < 0) continue;
        }
        *pm = m; *pk2 = k2; *pr = r;
        return 1;
    }
    return 0;
}

static int choose_k(const long *trials, const long *wins) {
    if (rndu() < 0.2) return 1 + rndint(MAXK);
    double bs = -1.0;
    int k = 1;
    for (int kk = 1; kk <= MAXK; kk++) {
        double s = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rndu();
        if (s > bs) { bs = s; k = kk; }
    }
    return k;
}

/* Generate a random candidate lift of base size k that is larger than bn. */
static int gen_cand(Cand *c, int k, int bn) {
    int base = bn / (2 * k);
    int spread = base / 8 + 1;
    int target = base + 1 + rndint(spread);
    if (target < 2) target = 2;
    int m, k2;
    long long r;
    if (!sample_group(target, &m, &k2, &r)) return 0;
    set_group(m, k2, r);
    long long Gl = grp.G;
    long long NN = 2LL * k * Gl;
    if (NN <= bn) return 0;
    c->m = m; c->k2 = k2; c->r = r; c->K = k;
    c->ord = (int)NN;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < k; i++) c->layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = c->layers[l][i];
            c->layers[l][i] = c->layers[l][j];
            c->layers[l][j] = tmp;
        }
        for (int i = 0; i < k; i++) c->S[l][i] = rndint((int)Gl);
    }
    c->Tmax = 8000 + 40 * (long)NN;
    c->steps = 0;
    c->cost = cand_load(c);
    c->c0 = c->cost > 1 ? (double)c->cost : 1.0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    DEG = d;
    D_ = D;
    rs = 0x9E3779B97F4A7C15ULL ^ (u64)(seed * 2654435761UL + 12345UL);
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();
    (void)gmul_dummy_guard;

    double start = now(), deadline = start + tl;
    best_n = n0;
    best_m = 0;
    best_e = NULL;

    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
    static Cand pool[POOL];
    int fails = 0;

    while (now() < deadline) {
        int np = 0;
        for (int a = 0; a < 20 * POOL && np < POOL && now() < deadline; a++) {
            int k = choose_k(trials, wins);
            if (gen_cand(&pool[np], k, best_n)) {
                np++;
                trials[k]++;
            }
        }
        if (np == 0) {
            if (++fails > 200) break;
            continue;
        }
        fails = 0;

        long maxN = 0;
        for (int i = 0; i < np; i++) if (pool[i].ord > maxN) maxN = pool[i].ord;
        long s0 = 400 + maxN / 6;

        long B = s0;
        int alive = np;
        int found = 0;
        while (alive > 0 && !found && now() < deadline) {
            for (int i = 0; i < alive && now() < deadline; i++) {
                Cand *c = &pool[i];
                long long cur = cand_load(c);
                long done = 0;
                long long cost = anneal_run(cur, c->c0, B, c->steps, c->Tmax, deadline, &done);
                c->steps += done;
                c->cost = cost;
                cand_save(c);
                if (cost == 0) {
                    record_solution();
                    wins[c->K]++;
                    found = 1;
                    break;
                }
            }
            if (found) break;

            /* Sort the alive candidates by cost, best first. */
            for (int i = 1; i < alive; i++) {
                Cand tmp = pool[i];
                int j = i - 1;
                while (j >= 0 && pool[j].cost > tmp.cost) {
                    pool[j + 1] = pool[j];
                    j--;
                }
                pool[j + 1] = tmp;
            }
            if (alive > 1) alive = (alive + 1) / 2;
            B *= 2;
            if (alive == 1 && B > 32 * s0) break;
        }
    }

    emit_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Algebraic baselines.
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
# Slack extension: add vertices using spare degree; every kept graph is valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Python fallback: bi-Cayley annealing over Z_m x| Z_k2 (used if C is unavailable).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def _py_search(d, D, rng, deadline, get_best_n, consider):
    """Python bi-Cayley annealing over base sizes k, until the deadline."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    while time.monotonic() < deadline:
        if rng.random() < 0.2:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())
        cur = get_best_n()
        base = cur // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= cur:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main engine: C successive-halving search over bi-Cayley lifts, seeded with the current best order.
    if d >= 2 and time.monotonic() < deadline - 3.0:
        remaining = deadline - time.monotonic()
        c_budget = max(1.0, remaining - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2), best_n],
                            stdin_graph=None, timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Python fallback / tail search for the rest of the budget.
    if time.monotonic() < deadline - 1.0:
        _py_search(d, D, rng, deadline, lambda: best_n, consider)

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
