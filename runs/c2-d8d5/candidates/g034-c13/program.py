"""Bold variant: vertex-transitive bi-Cayley lifts over semidirect products, searched in C
with a BFS-from-representatives cost, then the parent's Python bi-Cayley phase as a backup."""
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# Python bi-Cayley lifts over semidirect products (parent's search, kept as backup).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation exit. Returns (n, edges) or None."""
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


def _bicayley_phase(best, d, D, rng, deadline, consider_fn):
    """Bandit over base sizes k; each trial tries to beat the current best order."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        best_n = best[0]
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
            new = consider_fn(res[0], res[1])
            if new is not None:
                best = new
    return best


# ----------------------------------------------------------------------------
# C engine: vertex-transitive bi-Cayley lifts. A lift has k blocks per side, each of
# size N = |Z_m x| Z_k2|, and d layers. Layer l joins A_i to B_{sig_l(i)} by
# A_{i,g} ~ B_{sig,g*s}. Left multiplication is an automorphism, so the diameter
# check is a BFS from one representative per block (2k BFS in total).
# Simulated annealing over permutations and voltages; cost = unreached pairs.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Vertex-transitive bi-Cayley lift search.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * stdout: "n m" + edges of the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 16384
#define MAXD 16
#define MAXK 4
#define MAXN 2048
#define MAXC 65536
#define ITERS 30000

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x| Z_kk, element a*kk+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod kk). */
static int gm, gk, gN, gr;
static int rp[MAXN];
static int ginvt[MAXN];

static void set_group(int m, int kk, int r) {
    gm = m;
    gk = kk;
    gN = m * kk;
    gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < kk; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < gN; x++) {
        int a = x / kk, b = x % kk, nb = (kk - b) % kk;
        int ia = (int)((m - ((long)rp[nb] * a) % m) % m);
        ginvt[x] = ia * kk + nb;
    }
}

/* out[g] = g * s for all g in the group. */
static void fill_mul(int s, int *out) {
    int c = s / gk, e = s % gk;
    for (int b = 0; b < gk; b++) {
        int t = (int)((long)rp[b] * c % gm);
        int be = (b + e) % gk;
        for (int a = 0; a < gm; a++) {
            int x = a + t;
            if (x >= gm) x -= gm;
            out[a * gk + b] = x * gk + be;
        }
    }
}

/* Configuration. */
static int kb, nv;
static int sig[MAXD][MAXK], vol[MAXD][MAXK];
static int nbr[MAXV][MAXD];
static int tmpA[MAXN], tmpB[MAXN];

static void set_layer(int l) {
    int N = gN;
    for (int i = 0; i < kb; i++) {
        int j = sig[l][i], s = vol[l][i];
        fill_mul(s, tmpA);
        for (int g = 0; g < N; g++) nbr[i * N + g][l] = (kb + j) * N + tmpA[g];
        fill_mul(ginvt[s], tmpB);
        for (int h = 0; h < N; h++) nbr[(kb + j) * N + h][l] = i * N + tmpB[h];
    }
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < kb; i++) p[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < kb; i++) {
            sig[l][i] = p[i];
            vol[l][i] = rndint(gN);
        }
        set_layer(l);
    }
}

static void swap_sig(int l, int i1, int i2) {
    int t = sig[l][i1];
    sig[l][i1] = sig[l][i2];
    sig[l][i2] = t;
}

/* Duplicate edges: same (block i, target block, voltage) used by two layers. */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < kb; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l][i] == sig[l2][i] && vol[l][i] == vol[l2][i]) c++;
    return c;
}

static int mark[MAXV];
static int stampc = 0;
static int qu[MAXV];

/* Vertices at distance > D from src. */
static int bfs_unreached(int src) {
    stampc++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    mark[src] = stampc;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qu[head++];
            for (int l = 0; l < d; l++) {
                int u = nbr[v][l];
                if (mark[u] != stampc) {
                    mark[u] = stampc;
                    qu[tail++] = u;
                }
            }
        }
    }
    return nv - tail;
}

/* Zero iff every vertex is within D of every block representative (hence valid). */
static long eval_cost(void) {
    long c = 0;
    for (int r = 0; r < 2 * kb; r++) c += bfs_unreached(r * gN);
    c += (long)gN * dupcount();
    return c;
}

static long anneal(int iters) {
    long cur = eval_cost();
    double T0 = 2.0, T1 = 0.2;
    for (int t = 0; t < iters && cur > 0; t++) {
        if ((t & 127) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)t / iters);
        int l = rndint(d);
        if (kb > 1 && rnd01() < 0.3) {
            int i1 = rndint(kb), i2 = rndint(kb - 1);
            if (i2 >= i1) i2++;
            swap_sig(l, i1, i2);
            set_layer(l);
            long c = eval_cost();
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
                cur = c;
            } else {
                swap_sig(l, i1, i2);
                set_layer(l);
            }
        } else {
            int i = rndint(kb);
            int old = vol[l][i];
            int nvv = rndint(gN);
            if (nvv == old) continue;
            vol[l][i] = nvv;
            set_layer(l);
            long c = eval_cost();
            if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
                cur = c;
            } else {
                vol[l][i] = old;
                set_layer(l);
            }
        }
    }
    return cur;
}

static int best_n = 0;
static int bk, bm, bkk, br, bN;
static int bsig[MAXD][MAXK], bvol[MAXD][MAXK];
static int cand_m[MAXC], cand_k[MAXC], cand_r[MAXC];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long moore = moore_bound();
    static const int kchoice[6] = {1, 1, 2, 2, 3, 4};

    while (now() < t_end) {
        if (best_n >= moore) break;
        int k = kchoice[rndint(6)];
        long Nmin = (best_n + 2 + 2L * k - 1) / (2L * k);
        if (Nmin < d) Nmin = d;
        long Nl = Nmin + rndint((int)(1 + Nmin / 40));
        if (Nl > MAXN || 2L * k * Nl > MAXV || 2L * k * Nl > moore) continue;
        int N = (int)Nl;

        int nc = 0;
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int kk = N / m;
            if (m == 1) {
                if (nc < MAXC) {
                    cand_m[nc] = 1; cand_k[nc] = kk; cand_r[nc] = 0; nc++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, kk, m) != 1 % m) continue;
                if (nc < MAXC) {
                    cand_m[nc] = m; cand_k[nc] = kk; cand_r[nc] = r; nc++;
                }
            }
        }
        if (nc == 0) continue;
        int pick = rndint(nc);
        set_group(cand_m[pick], cand_k[pick], cand_r[pick]);
        kb = k;
        nv = 2 * kb * gN;

        random_config();
        if (anneal(ITERS) == 0) {
            best_n = nv;
            bk = kb;
            bm = gm;
            bkk = gk;
            br = gr;
            bN = gN;
            memcpy(bsig, sig, sizeof sig);
            memcpy(bvol, vol, sizeof vol);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    kb = bk;
    set_group(bm, bkk, br);
    nv = 2 * kb * gN;
    memcpy(sig, bsig, sizeof sig);
    memcpy(vol, bvol, sizeof vol);
    for (int l = 0; l < d; l++) set_layer(l);
    if (eval_cost() != 0 || nv != best_n) {
        printf("0 0\n");
        return 0;
    }
    long m = (long)kb * gN * d;
    printf("%d %ld\n", nv, m);
    for (int v = 0; v < kb * gN; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[v][l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Return the new graph if it is a larger valid graph, else None."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return best
        return None

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                if d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass

    # Search: new C engine first, then the Python bi-Cayley phase with the remaining time.
    if D >= 2 and 2 <= d <= 16 and time.monotonic() < end - 3:
        c_budget = 0.6 * (end - time.monotonic())
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                             stdin_graph=None, timeout=c_budget + 8)
            out = lib.parse_graph_text(text)
            consider(out[0], out[1])
        except (RuntimeError, ValueError):
            pass
        try:
            best = _bicayley_phase(best, d, D, rng, end, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
