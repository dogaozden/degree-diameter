"""Bi-Cayley lift search with a C annealing engine and block-extension warm starts.

New in this version:
  * C engine (_C_SOURCE) anneals voltages and layer permutations over Z_m x| Z_k2
    for a fixed base size k. It is far faster than the numpy search.
  * Block-extension warm start: a valid lift at base size k (group G) is extended to
    base size k+1 with the SAME group. The old voltages and layers are kept, a new
    block is appended, and the C engine anneals from there. This adds 2G vertices per
    step and reuses the structure of the solution it already found.
  * Python annealing is kept only as a fallback if the C path fails.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 15
#define PENALTY 1000LL
#define PATIENCE 3000LL

/* Bi-Cayley lift over G = Z_M x| Z_K2 with element g = a*K2 + b and
 * (a,b)(c,e) = (a + r^b c, b + e).  Base has K vertices per side, DG layers.
 * Vertex A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h.
 * Layer l pairs A_i with B_{layer[l][i]} by voltage volt[l][i]:
 *   A_{i,g} ~ B_{p, g*s},  i.e. B_{p,h} ~ A_{i, h*s^{-1}}.
 * Every layer is a permutation, so each vertex has degree DG.
 * Diameter is checked from the K-block representatives of every block.
 */

static int DG, DM, K, M, K2, G, N, R;
static int *PW;
static int *layer, *lay_inv, *volt, *nbr;
static uint32_t *buf1, *buf2, *cur, *prop;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static inline int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rndd(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static inline int popc(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static inline int gmul(int g, int s) {
    int a = g / K2, b = g % K2, c = s / K2, e = s % K2;
    long long t = ((long long)PW[b] * c) % M;
    int aa = (int)(((long long)a + t) % M);
    return aa * K2 + (b + e) % K2;
}

/* returns g with g*s = h */
static inline int gsolve(int s, int h) {
    int c = s / K2, e = s % K2, a2 = h / K2, b2 = h % K2;
    int b = ((b2 - e) % K2 + K2) % K2;
    long long t = ((long long)PW[b] * c) % M;
    long long a = (((long long)a2 - t) % M + M) % M;
    return (int)a * K2 + b;
}

static void set_dart(int l, int i) {
    int p = layer[l * K + i], s = volt[l * K + i];
    int *nb = nbr + (size_t)l * N;
    int A0 = i * G, B0 = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nb[A0 + g] = B0 + gmul(g, s);
        nb[B0 + g] = A0 + gsolve(s, g);
    }
}

static void rebuild_inv(void) {
    for (int l = 0; l < DG; l++)
        for (int i = 0; i < K; i++)
            lay_inv[l * K + layer[l * K + i]] = i;
}

static void build_all(void) {
    for (int l = 0; l < DG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i);
}

static void randomize_state(void) {
    for (int l = 0; l < DG; l++) {
        int *row = layer + (size_t)l * K;
        for (int i = 0; i < K; i++) row[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = row[i];
            row[i] = row[j];
            row[j] = t;
        }
        for (int i = 0; i < K; i++) volt[l * K + i] = rndi(G);
    }
    rebuild_inv();
    build_all();
}

/* P = [1, kold, layers (DG x kold), volts (DG x kold), ...]
 * Extends the old state to K blocks: each new block i maps A_i to B_i
 * in every layer (keeps permutations) with random voltages. */
static int load_warm(const int *P, int kold) {
    int idx = 2;
    for (int l = 0; l < DG; l++)
        for (int i = 0; i < kold; i++) {
            int p = P[idx++];
            if (p < 0 || p >= kold) return 0;
            layer[l * K + i] = p;
        }
    for (int l = 0; l < DG; l++)
        for (int i = 0; i < kold; i++) {
            int s = P[idx++];
            if (s < 0 || s >= G) return 0;
            volt[l * K + i] = s;
        }
    for (int l = 0; l < DG; l++)
        for (int i = kold; i < K; i++) {
            layer[l * K + i] = i;
            volt[l * K + i] = rndi(G);
        }
    rebuild_inv();
    build_all();
    return 1;
}

static void swap_layer(int l, int i1, int i2) {
    int *row = layer + (size_t)l * K;
    int t = row[i1];
    row[i1] = row[i2];
    row[i2] = t;
    lay_inv[l * K + row[i1]] = i1;
    lay_inv[l * K + row[i2]] = i2;
    set_dart(l, i1);
    set_dart(l, i2);
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DG; l++)
            for (int l2 = l + 1; l2 < DG; l2++)
                if (layer[l * K + i] == layer[l2 * K + i] &&
                    volt[l * K + i] == volt[l2 * K + i])
                    dup++;
    return dup;
}

/* out[v] = bitmask of block representatives within distance DM of v */
static void compute_reach(uint32_t *out) {
    uint32_t *a = buf1, *b = buf2;
    for (int v = 0; v < N; v++) a[v] = 0;
    for (int bb = 0; bb < 2 * K; bb++) a[bb * G] = 1u << bb;
    for (int t = 0; t < DM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = a[v];
            for (int l = 0; l < DG; l++) x |= a[nbr[(size_t)l * N + v]];
            b[v] = x;
            if (x != a[v]) changed = 1;
        }
        uint32_t *tmp = a;
        a = b;
        b = tmp;
        if (!changed) break;
    }
    memcpy(out, a, sizeof(uint32_t) * (size_t)N);
}

static long long eval_cost(uint32_t *out) {
    compute_reach(out);
    long long c = 0;
    int full = 2 * K;
    for (int v = 0; v < N; v++) c += full - popc(out[v]);
    return c + PENALTY * (long long)dupcount();
}

static int accept(long long c2, long long cost, double temp) {
    if (c2 <= cost) return 1;
    return rndd() < exp(-(double)(c2 - cost) / temp);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: d D k m k2 r seed seconds\n");
        return 1;
    }
    DG = atoi(argv[1]);
    DM = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double secs = atof(argv[8]);
    if (DG < 1 || DM < 1 || K < 1 || K > MAXK || M < 2 || K2 < 1) {
        printf("0 0\n");
        return 0;
    }
    R %= M;
    G = M * K2;
    N = 2 * K * G;
    PW = malloc(sizeof(int) * (size_t)K2);
    PW[0] = 1 % M;
    for (int b = 1; b < K2; b++) PW[b] = (int)(((long long)PW[b - 1] * R) % M);

    long long n0 = 0, m0 = 0;
    int *P = NULL;
    long long np = 0;
    if (scanf("%lld %lld", &n0, &m0) == 2 && m0 > 0) {
        np = 2 * m0;
        P = malloc(sizeof(int) * (size_t)np);
        for (long long i = 0; i < np; i++) {
            long long x = 0;
            if (scanf("%lld", &x) != 1) x = 0;
            P[i] = (int)x;
        }
    }
    (void)n0;

    layer = malloc(sizeof(int) * (size_t)DG * K);
    lay_inv = malloc(sizeof(int) * (size_t)DG * K);
    volt = malloc(sizeof(int) * (size_t)DG * K);
    nbr = malloc(sizeof(int) * (size_t)DG * N);
    buf1 = malloc(sizeof(uint32_t) * (size_t)N);
    buf2 = malloc(sizeof(uint32_t) * (size_t)N);
    cur = malloc(sizeof(uint32_t) * (size_t)N);
    prop = malloc(sizeof(uint32_t) * (size_t)N);

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 16; i++) rnd64();

    int warm = 0;
    if (P && np >= 2 && P[0] == 1) {
        int kold = P[1];
        if (kold >= 1 && kold <= K && np >= 2 + 2LL * DG * kold) {
            warm = load_warm(P, kold);
        }
    }
    if (!warm) randomize_state();

    long long cost = eval_cost(cur);
    long long best_run = cost;
    double c0 = cost > 1 ? (double)cost : 1.0;
    double T0 = 0.01 * c0;
    if (T0 < 1.0) T0 = 1.0;
    double temp = T0;
    uint32_t FULL = (uint32_t)((1ULL << (2 * K)) - 1ULL);
    long long it = 0, last_imp = 0;
    int found = (cost == 0);
    clock_t t0 = clock();

    while (!found) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            double frac = el / secs;
            temp = T0 * (1.0 - frac);
            if (temp < 0.3) temp = 0.3;
        }
        it++;
        if (it - last_imp > PATIENCE) {
            randomize_state();
            cost = eval_cost(cur);
            best_run = cost;
            last_imp = it;
            if (cost == 0) found = 1;
            continue;
        }

        if (K >= 2 && rndd() < 0.25) {
            /* layer swap move */
            int l = rndi(DG);
            int i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            long long c2 = eval_cost(prop);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(cur, prop, sizeof(uint32_t) * (size_t)N);
            } else {
                swap_layer(l, i1, i2);
                continue;
            }
        } else {
            /* voltage move, defect-targeted with probability 0.4 */
            int l, i;
            int bad = -1;
            if (rndd() < 0.4) {
                for (int tr = 0; tr < 64; tr++) {
                    int v = rndi(N);
                    if (cur[v] != FULL) {
                        bad = v;
                        break;
                    }
                }
            }
            if (bad >= 0) {
                int block = bad / G;
                l = rndi(DG);
                if (block < K) i = block;
                else i = lay_inv[l * K + (block - K)];
            } else {
                l = rndi(DG);
                i = rndi(K);
            }
            int idx = l * K + i;
            int old = volt[idx];
            int nw = rndi(G);
            if (nw == old) continue;
            volt[idx] = nw;
            set_dart(l, i);
            long long c2 = eval_cost(prop);
            if (accept(c2, cost, temp)) {
                cost = c2;
                memcpy(cur, prop, sizeof(uint32_t) * (size_t)N);
            } else {
                volt[idx] = old;
                set_dart(l, i);
                continue;
            }
        }

        if (cost < best_run) {
            best_run = cost;
            last_imp = it;
        }
        if (cost == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    long long edges = (long long)K * G * DG;
    printf("%d %lld\n", N, edges);
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < DG; l++)
            printf("%d %d\n", v, nbr[(size_t)l * N + v]);
    printf("STATE %d\n", K);
    for (int l = 0; l < DG; l++) {
        for (int i = 0; i < K; i++) printf(" %d", layer[l * K + i]);
        printf("\n");
    }
    for (int l = 0; l < DG; l++) {
        for (int i = 0; i < K; i++) printf(" %d", volt[l * K + i]);
        printf("\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact baseline families (unchanged from the parent).
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
# Group and table helpers for the Python fallback search.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_KMAX = 8


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
                r = None
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex over the 2k block representatives."""
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Python simulated annealing (fallback). Returns (n, edges) or None."""
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


# ----------------------------------------------------------------------------
# C engine driver with block-extension warm starts.
# ----------------------------------------------------------------------------

def _c_call(d, D, k, m, k2, r, seed, secs, warm):
    """Run the C annealer once. warm = None or (kold, layers, volts) from a previous state.

    Returns (n, edges, state) or None. state = (k, layers, volts) for chaining.
    """
    stdin = None
    if warm is not None:
        kold, L, V = warm
        P = [1, kold]
        for row in L:
            P.extend(row[:kold])
        for row in V:
            P.extend(row[:kold])
        if len(P) % 2:
            P.append(0)
        # Encoded as a fake graph: run_c writes "0 m" and m pairs, so C reads 2m ints.
        stdin = (0, [(P[i], P[i + 1]) for i in range(0, len(P), 2)])
    out = lib.run_c(_C_SOURCE, [d, D, k, m, k2, r, seed, f"{secs:.3f}"],
                    stdin_graph=stdin, timeout=secs + 20.0)
    tok = out.split()
    if len(tok) < 2:
        return None
    n, mm = int(tok[0]), int(tok[1])
    if n <= 0 or mm <= 0 or len(tok) < 2 + 2 * mm:
        return None
    body = tok[2:2 + 2 * mm]
    edges = [(int(body[2 * i]), int(body[2 * i + 1])) for i in range(mm)]
    rest = tok[2 + 2 * mm:]
    state = None
    if len(rest) >= 2 and rest[0] == "STATE":
        kk = int(rest[1])
        vals = [int(x) for x in rest[2:]]
        off = d * kk
        L = [vals[l * kk:(l + 1) * kk] for l in range(d)]
        V = [vals[off + l * kk:off + (l + 1) * kk] for l in range(d)]
        state = (kk, L, V)
    return n, edges, state


def _c_search(d, D, rng, deadline):
    """Cold anneals over groups plus block-extension warm starts. Returns (results, error)."""
    results = []
    err = None
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    best_guess = max(2 * d, int(0.2 * lib.moore_bound(d, D)))

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    try:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 2.5:
                break
            k = pick_k()
            base = max(1, best_guess // (2 * k))
            target = base + 1 + rng.randrange(0, max(2, base // 16 + 2))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            trials[k] += 1
            secs = min(remaining - 1.5, 7.0)
            res = _c_call(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), secs, None)
            if res is None:
                continue
            wins[k] += 1
            n, e, state = res
            results.append((n, e))
            best_guess = max(best_guess, n)

            # Block extension: same group, base size grows by one block (adds 2G vertices).
            cur, kk = state, k
            while cur is not None and kk < _KMAX:
                remaining = deadline - time.monotonic()
                secs = min(remaining - 1.5, 6.0)
                if secs < 0.5:
                    break
                kk += 1
                res2 = _c_call(d, D, kk, m, k2, r, rng.randrange(1, 1 << 30), secs, cur)
                if res2 is None:
                    break
                results.append((res2[0], res2[1]))
                best_guess = max(best_guess, res2[0])
                cur = res2[2]
    except Exception as ex:  # keep whatever was found; the caller may fall back
        err = ex
    return results, err


def _py_search(d, D, rng, deadline, best, consider):
    """Python fallback (parent's annealing loop)."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        best_n = best[0][0]
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
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
    span = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    search_end = start + span
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = [lib.haar_graph(d, range(d))]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Exact constructions (calibration cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best[0]
    if D == 4 and time.monotonic() < search_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best[0]

    # Main search: C annealer with block-extension warm starts.
    c_end = search_end - min(8.0, 0.15 * span)
    results = []
    if time.monotonic() < c_end - 3.0:
        results, _err = _c_search(d, D, rng, c_end)
        for n, e in sorted(results, key=lambda t: -t[0]):
            consider(n, e)

    # Python fallback only if the C path produced nothing.
    if not results and time.monotonic() < search_end - 2.0:
        _py_search(d, D, rng, search_end, best, consider)

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0]
