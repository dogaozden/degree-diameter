import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: local search over Haar graphs H(G, S) of a finite group G, where
# S is a set of d distinct group elements. Vertices a_x = x and b_y = G + y,
# with a_x ~ b_{x*s} for s in S. Left multiplication is an automorphism, so the
# diameter is at most D iff BFS of depth D from a_e and from b_e reaches all.
# Input (stdin): "G G*G" then G*G lines "product index", where
# mult[index] = product, index = x*G + y, identity = 0.
# Output: a valid graph "n m" with edges, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int G, DEG, DIAM;
static int *mulT;
static int *invT;
static int *S;
static int *vis;
static int *qu;
static int stampc = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int bfs_reach(int src) {
    int tail = 0, fs = 0, fe = 1, level;
    stampc++;
    if (stampc == 0x7fffffff) {
        memset(vis, 0, sizeof(int) * (size_t)(2 * G));
        stampc = 1;
    }
    vis[src] = stampc;
    qu[tail++] = src;
    for (level = 0; level < DIAM && fs < fe; level++) {
        int h;
        for (h = fs; h < fe; h++) {
            int u = qu[h];
            int t;
            if (u < G) {
                for (t = 0; t < DEG; t++) {
                    int v = G + mulT[u * G + S[t]];
                    if (vis[v] != stampc) {
                        vis[v] = stampc;
                        qu[tail++] = v;
                    }
                }
            } else {
                int y = u - G;
                for (t = 0; t < DEG; t++) {
                    int v = mulT[y * G + invT[S[t]]];
                    if (vis[v] != stampc) {
                        vis[v] = stampc;
                        qu[tail++] = v;
                    }
                }
            }
        }
        fs = fe;
        fe = tail;
    }
    return tail;
}

static int cost(void) {
    int N = 2 * G;
    int ca = bfs_reach(0);
    int cb = bfs_reach(G);
    return (N - ca) + (N - cb);
}

static void random_S(void) {
    int t, j;
    for (t = 0; t < DEG; t++) {
        int x, ok;
        do {
            x = rnd_int(G);
            ok = 1;
            for (j = 0; j < t; j++) {
                if (S[j] == x) { ok = 0; break; }
            }
        } while (!ok);
        S[t] = x;
    }
}

int main(int argc, char **argv) {
    int n, m, i, x, y, t;
    double tl, start;
    long long it = 0, since = 0;
    int cur, bestc;

    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tl = atof(argv[4]);

    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    G = n;
    if (G < 2 || G > 2000 || m != G * G || DEG < 1 || DEG > G || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    mulT = calloc((size_t)m, sizeof(int));
    invT = calloc((size_t)G, sizeof(int));
    S = calloc((size_t)DEG, sizeof(int));
    vis = calloc((size_t)(2 * G), sizeof(int));
    qu = calloc((size_t)(2 * G), sizeof(int));
    if (!mulT || !invT || !S || !vis || !qu) { printf("0 0\n"); return 0; }

    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || u >= G || v < 0 || v >= m) { printf("0 0\n"); return 0; }
        mulT[v] = u;
    }

    for (x = 0; x < G; x++) {
        if (mulT[x] != x || mulT[x * G] != x) { printf("0 0\n"); return 0; }
    }
    for (x = 0; x < G; x++) {
        int found = -1;
        for (y = 0; y < G; y++) {
            if (mulT[x * G + y] == 0) { found = y; break; }
        }
        if (found < 0) { printf("0 0\n"); return 0; }
        invT[x] = found;
    }

    random_S();
    cur = cost();
    bestc = cur;
    start = (double)clock() / CLOCKS_PER_SEC;

    while (cur > 0) {
        int old, nx, ok, j, c;
        if ((it & 255) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - start;
            if (el > tl) break;
        }
        it++;
        t = rnd_int(DEG);
        old = S[t];
        nx = rnd_int(G);
        if (nx == old) continue;
        ok = 1;
        for (j = 0; j < DEG; j++) {
            if (j != t && S[j] == nx) { ok = 0; break; }
        }
        if (!ok) continue;
        S[t] = nx;
        c = cost();
        if (c <= cur || rnd_int(1000) < 25) {
            cur = c;
        } else {
            S[t] = old;
        }
        if (cur < bestc) {
            bestc = cur;
            since = 0;
        } else {
            since++;
        }
        if (since > 200000) {
            random_S();
            cur = cost();
            bestc = cur;
            since = 0;
        }
    }

    if (cur == 0) {
        printf("%d %d\n", 2 * G, G * DEG);
        for (x = 0; x < G; x++) {
            for (t = 0; t < DEG; t++) {
                printf("%d %d\n", x, G + mulT[x * G + S[t]]);
            }
        }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


MAX_G_CAP = 400


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x| Z_k, and PSL(2,7), PGL(2,7) as matrix groups.
# ----------------------------------------------------------------------------

def _matrix_mul(X, Y, p):
    a, b, c, d = X
    e, f, g, h = Y
    return ((a * e + b * g) % p, (a * f + b * h) % p,
            (c * e + d * g) % p, (c * f + d * h) % p)


def _matrix_norm(M, p, special):
    vec = tuple(x % p for x in M)
    v = next(x for x in vec if x)
    if special:
        if v > p // 2:
            vec = tuple((-x) % p for x in vec)
    else:
        inv = pow(v, p - 2, p)
        vec = tuple((x * inv) % p for x in vec)
    return vec


def _matrix_group(p, special):
    """Return (order, table) for PSL(2,p) (special=True) or PGL(2,p); identity has index 0."""
    if special:
        gens = [(1, 1, 0, 1), (0, p - 1, 1, 0)]
    else:
        prim = next(x for x in range(2, p)
                    if len({pow(x, i, p) for i in range(1, p)}) == p - 1)
        gens = [(1, 1, 0, 1), (0, 1, 1, 0), (prim, 0, 0, 1)]
    gens = [_matrix_norm(g, p, special) for g in gens]
    ident = _matrix_norm((1, 0, 0, 1), p, special)
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        e = elems[i]
        i += 1
        for g in gens:
            f = _matrix_norm(_matrix_mul(e, g, p), p, special)
            if f not in index:
                index[f] = len(elems)
                elems.append(f)
    G = len(elems)
    table = [0] * (G * G)
    for x in range(G):
        X = elems[x]
        for y in range(G):
            table[x * G + y] = index[_matrix_norm(_matrix_mul(X, elems[y], p), p, special)]
    return G, table


def _table(spec):
    """Return (order, table) with table[x*order + y] = x*y, identity 0."""
    if spec[0] == "sd":
        _, m, k, r = spec
        order, mul, _ = lib.semidirect_group(m, k, r)
        return order, [mul(x, y) for x in range(order) for y in range(order)]
    return _matrix_group(spec[1], special=(spec[0] == "psl"))


def _group_specs(max_g):
    """Map order G -> list of group specs with that order (2 <= G <= max_g)."""
    rng = random.Random(7)
    by_g = {}

    def add(g, spec):
        by_g.setdefault(g, []).append(spec)

    for m in range(2, max_g + 1):
        for k in range(1, max_g // m + 1):
            g = m * k
            add(g, ("sd", m, k, 1))
            if k >= 2:
                rs = [r for r in range(2, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
                if len(rs) > 3:
                    rs = rng.sample(rs, 3)
                for r in rs:
                    add(g, ("sd", m, k, r))
    if max_g >= 168:
        add(168, ("psl", 7))
    if max_g >= 336:
        add(336, ("pgl", 7))
    return by_g


# ----------------------------------------------------------------------------
# Safe fallbacks.
# ----------------------------------------------------------------------------

def _fallbacks(d, D):
    cands = [(1, []), (2, [(0, 1)]), lib.haar_graph(d, range(d))]  # K_{d,d}
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    return cands


# ----------------------------------------------------------------------------
# Ladder search over group orders: adaptive step, each attempt runs the C engine.
# ----------------------------------------------------------------------------

def _ladder(d, D, seed, deadline, res):
    moore = lib.moore_bound(d, D)
    max_g = min(MAX_G_CAP, moore // 2)
    by_g = _group_specs(max_g)
    gs = sorted(g for g in by_g if g >= max(2, d))
    rng = random.Random(seed * 7919 + 1)

    lo = res[0][0] // 2   # a Haar graph over a group of order lo is already held
    step = 1
    fails = {}

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        cand = [g for g in gs if g > lo and fails.get(g, 0) < 2]
        if not cand:
            break
        target = lo + step
        G = next((g for g in cand if g >= target), cand[0])
        spec = rng.choice(by_g[G])
        try:
            order, table = _table(spec)
        except ValueError:
            fails[G] = fails.get(G, 0) + 1
            continue

        slice_s = min(remaining - 1.0, 4.0 + 2.5 * fails.get(G, 0))
        if slice_s < 0.5:
            break
        edges = [(table[k], k) for k in range(order * order)]
        run_seed = (seed * 1000003 + G * 31 + 17) % 2147483647
        try:
            out = lib.run_c(C_SOURCE, [d, D, run_seed, round(slice_s, 2)],
                            stdin_graph=(order, edges), timeout=slice_s + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            break

        if n > res[0][0] and lib.is_valid(n, e, d, D):
            res[0] = (n, e)
            lo = n // 2
            step = min(step * 2, 32)
        else:
            fails[G] = fails.get(G, 0) + 1
            step = max(1, step // 2)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    deadline = t0 + max(1.0, 0.8 * time_limit - 1.0)

    res = [(1, [])]
    try:
        for n, e in _fallbacks(d, D):
            if n > res[0][0] and lib.is_valid(n, e, d, D):
                res[0] = (n, e)
    except Exception:
        pass

    if D >= 2:
        try:
            _ladder(d, D, seed, deadline, res)
        except Exception:
            pass

    n, e = res[0]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
