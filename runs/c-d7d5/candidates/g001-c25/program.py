import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (unchanged from the parent).
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
# Python bi-Cayley annealing (parent search, kept as a fallback).
# ----------------------------------------------------------------------------

_PENALTY = 1000


def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, perms):
    """Unreached (representative, vertex) pairs plus duplicate-dart penalties. Zero means valid."""
    seen = set()
    dup = 0
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen:
            dup += 1
        seen.add(key)
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen_v = [False] * N
        seen_v[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen_v[v]:
                        seen_v[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total + _PENALTY * dup


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, p[i], rng.randrange(G)] for p in layers for i in range(k)]
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_pm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _cost(k, G, D, darts, perms)
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_pm

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Bold new engine: C simulated annealing over bi-Cayley lifts.
#
# Vertices: A(i,g) = i*G + g, B(j,h) = (K+j)*G + h, with G = |Z_m x| Z_k2|.
# Each of the DEG layers l is a permutation J_l of range(K) together with a
# voltage s per source: A(i,g) ~ B(J_l(i), g*s). Each vertex gets exactly one
# edge per layer, so the graph is DEG-regular before duplicate removal, and
# it is bipartite by construction. Left multiplication is an automorphism,
# so the diameter check only needs BFS from the 2K representatives r*G.
# Moves: change one voltage, or swap two targets within one layer.
# Groups and K are sampled per run, and the target order ratchets upward.
# ----------------------------------------------------------------------------

_FLOORS = {(7, 5): 1000}

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK2 64

static int DEG, DIAM, K, G, GM, GK2, N;
static int GR[MAXK2];
static int *Jt, *St, *adj;
static unsigned *vis;
static unsigned stamp_ = 0;
static int *qu;
static uint64_t rs = 88172645463325252ULL;
static clock_t C_START;
static time_t T_START;

static int have = 0;
static int best_nn = 0, best_K = 0, best_G = 0;
static int *best_adj = NULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    double cpu = (double)(clock() - C_START) / (double)CLOCKS_PER_SEC;
    double wall = difftime(time(NULL), T_START);
    return cpu > wall ? cpu : wall;
}

/* Semidirect product Z_m x| Z_k2 with (a,b)(c,d) = (a + r^b c, b + d); element index a*k2 + b. */
static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2;
    int c = y / GK2, dd = y % GK2;
    int aa = (int)(((long long)a + (long long)GR[b] * c) % GM);
    int ee = (b + dd) % GK2;
    return aa * GK2 + ee;
}

/* Inverse of (a,b) is (-a r^(-b), -b), with r^(-b) = r^(k2-b). */
static int ginv(int x) {
    int a = x / GK2, b = x % GK2;
    int nb = (GK2 - b) % GK2;
    long long t = -((long long)a * GR[nb]) % GM;
    int c = (int)((t + GM) % GM);
    return c * GK2 + nb;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int setup_group(int Gt) {
    static const int K2S[] = {1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 9, 10, 12, 12, 14, 16, 18, 20, 24, 30, 36};
    int nk = (int)(sizeof K2S / sizeof K2S[0]);
    for (int att = 0; att < 60; att++) {
        int k2 = K2S[rndint(nk)];
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (k2 == 1) {
            GM = m;
            GK2 = 1;
            GR[0] = 1 % m;
            G = m;
            return 1;
        }
        int st = rndint(m), found = -1;
        for (int s = 0; s < m && found < 0; s++) {
            int r = (st + s) % m;
            if (gcd_i(r, m) != 1) continue;
            long long x = 1 % m;
            for (int j = 0; j < k2; j++) x = x * r % m;
            if (x == 1 % m) found = r;
        }
        if (found < 0) continue;
        GM = m;
        GK2 = k2;
        G = m * k2;
        GR[0] = 1 % m;
        for (int b = 1; b < k2; b++) GR[b] = (int)((long long)GR[b - 1] * found % m);
        return 1;
    }
    return 0;
}

static void init_state(void) {
    int *perm = malloc(sizeof(int) * (size_t)K);
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            Jt[l * K + i] = perm[i];
            St[l * K + i] = rndint(G);
        }
    }
    free(perm);
}

static void build_adj(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            int j = Jt[t];
            int s = St[t];
            int si = ginv(s);
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                adj[(size_t)a * DEG + l] = (K + j) * G + gmul(g, s);
            }
            for (int h = 0; h < G; h++) {
                int w = (K + j) * G + h;
                adj[(size_t)w * DEG + l] = i * G + gmul(h, si);
            }
        }
    }
}

static int bfs(int src) {
    stamp_++;
    if (stamp_ == 0) {
        memset(vis, 0, sizeof(unsigned) * (size_t)N);
        stamp_ = 1;
    }
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp_;
    for (int depth = 0; depth < DIAM && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            const int *a = adj + (size_t)qu[head++] * DEG;
            for (int e = 0; e < DEG; e++) {
                int v = a[e];
                if (vis[v] != stamp_) {
                    vis[v] = stamp_;
                    qu[tail++] = v;
                }
            }
        }
    }
    return tail;
}

static long long evaluate(void) {
    build_adj();
    long long tot = 0;
    for (int r = 0; r < 2 * K; r++) {
        tot += (long long)(N - bfs(r * G));
    }
    return tot;
}

static long long anneal(long long iters, double T0, double T1, double tlimit) {
    long long cur = evaluate();
    for (long long it = 0; it < iters && cur > 0; it++) {
        if (elapsed() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int mv = rndint(3);
        if (mv < 2 || K < 2) {
            int t = rndint(DEG * K);
            int old = St[t];
            int nv = rndint(G);
            if (nv == old) continue;
            St[t] = nv;
            long long c2 = evaluate();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                St[t] = old;
            }
        } else {
            int l = rndint(DEG);
            int i1 = rndint(K), i2 = rndint(K);
            if (i1 == i2) continue;
            int t1 = l * K + i1, t2 = l * K + i2;
            int tmp = Jt[t1];
            Jt[t1] = Jt[t2];
            Jt[t2] = tmp;
            long long c2 = evaluate();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                tmp = Jt[t1];
                Jt[t1] = Jt[t2];
                Jt[t2] = tmp;
            }
        }
    }
    return cur;
}

static void save_best(void) {
    size_t sz = (size_t)N * DEG;
    int *nb = malloc(sizeof(int) * sz);
    memcpy(nb, adj, sizeof(int) * sz);
    free(best_adj);
    best_adj = nb;
    best_nn = N;
    best_K = K;
    best_G = G;
    have = 1;
}

static void emit_best(void) {
    if (!have || !best_adj) {
        printf("0 0\n");
        return;
    }
    int NA = best_K * best_G;
    size_t cap = (size_t)NA * DEG;
    int *ed = malloc(sizeof(int) * (2 * cap + 4));
    int *tmp = malloc(sizeof(int) * (size_t)DEG);
    size_t m = 0;
    for (int u = 0; u < NA; u++) {
        memcpy(tmp, best_adj + (size_t)u * DEG, sizeof(int) * (size_t)DEG);
        for (int x = 1; x < DEG; x++) {
            int v = tmp[x], y = x - 1;
            while (y >= 0 && tmp[y] > v) {
                tmp[y + 1] = tmp[y];
                y--;
            }
            tmp[y + 1] = v;
        }
        for (int x = 0; x < DEG; x++) {
            if (x > 0 && tmp[x] == tmp[x - 1]) continue;
            ed[2 * m] = u;
            ed[2 * m + 1] = tmp[x];
            m++;
        }
    }
    printf("%d %zu\n", best_nn, m);
    for (size_t e = 0; e < m; e++) printf("%d %d\n", ed[2 * e], ed[2 * e + 1]);
    free(ed);
    free(tmp);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int base_n = argc > 5 ? atoi(argv[5]) : 0;
    int floor_n = argc > 6 ? atoi(argv[6]) : 0;

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();
    C_START = clock();
    T_START = time(NULL);

    if (DEG < 2 || DIAM < 2 || budget <= 0) {
        printf("0 0\n");
        return 0;
    }

    int cur_best = base_n;
    double tgt = (double)((floor_n > base_n + 2) ? floor_n : base_n + 2);
    int fails = 0;
    static const int KS[8] = {1, 2, 2, 3, 3, 4, 4, 5};

    while (elapsed() < budget) {
        int k = KS[rndint(8)];
        int n_goal = (int)tgt + 2 * rndint(5);
        if (n_goal < cur_best + 2) n_goal = cur_best + 2;
        int Gt = (n_goal + 2 * k - 1) / (2 * k);
        if (!setup_group(Gt)) continue;
        K = k;
        N = 2 * K * G;
        if (N <= cur_best) continue;

        Jt = malloc(sizeof(int) * (size_t)(DEG * K));
        St = malloc(sizeof(int) * (size_t)(DEG * K));
        adj = malloc(sizeof(int) * (size_t)N * DEG);
        vis = calloc((size_t)N, sizeof(unsigned));
        qu = malloc(sizeof(int) * (size_t)N);
        if (!Jt || !St || !adj || !vis || !qu) return 1;

        init_state();
        long long c = anneal(30000, 30.0, 0.3, budget);
        if (c == 0) {
            evaluate();
            save_best();
            cur_best = N;
            tgt = (double)(cur_best + 2);
            fails = 0;
        } else {
            fails++;
            if (fails >= 4) {
                tgt *= 0.98;
                fails = 0;
            }
        }

        free(Jt);
        free(St);
        free(adj);
        free(vis);
        free(qu);
        Jt = St = adj = NULL;
        vis = NULL;
        qu = NULL;
    }

    emit_best();
    return 0;
}
'''


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + total
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

    # Exact constructions: return immediately (calibration-style cases).
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

    # Bold branch: the C annealer over bi-Cayley lifts (most of the budget).
    if d >= 2 and D >= 2 and time.monotonic() < deadline - 3.0:
        c_budget = int(max(2.0, (deadline - time.monotonic()) * 0.8))
        floor_n = _FLOORS.get((d, D), 0)
        cseed = abs(int(seed)) % 1000000007
        try:
            out = lib.run_c(C_SOURCE, [d, D, cseed, c_budget, best_n, floor_n],
                            stdin_graph=None, timeout=c_budget + 25)
            n_c, e_c = lib.parse_graph_text(out)
            consider(n_c, e_c)
        except Exception:
            pass  # any C failure falls through to the Python search below

    # Parent's Python search for whatever time remains.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        order, mul = g
        res = _search(d, D, k, order, mul, rng, deadline, 500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
