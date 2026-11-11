"""Bi-Cayley graphs over non-abelian groups, searched by simulated annealing (d=4, D=7 target).

Change from the parent: instead of regular voltage lifts over explicit PSL/PGL groups with
orbit-reduced BFS, each candidate is a bi-Cayley graph over a non-abelian group G of order
N >= 421. Vertices a_x and b_x (x in G) join a_x to b_{x*s} for s in S, |S| = d. Left
multiplication is an automorphism, so the diameter is exact after two BFS (from a_e and b_e).
Groups come from GL(2,q), SL(2,q) for small q, direct products with cyclic groups, and
metacyclic groups Z_m x| Z_k. The C engine anneals over S for each group in one run.

Fallback: the best algebraic start (projective plane, W(q), H(3) when d=4) is kept unless a
strictly larger graph passes lib.is_valid.
"""
import itertools
import random
import time
from math import gcd

import numpy as np

import lib

RECORDS = {(4, 7): 840}
MAX_TABLE = 720
MAX_PAIRS = 1_200_000
MAX_GROUPS = 6

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define MAXV (2 * MAXN)
#define MAXDEG 16
#define TEMP 0.7
#define STALL 20000

/* Input (stdin): header "G m", then for each group "N K" followed by K pairs "u v",
 * where pair (x*N+y, z) means x*y = z in a group with identity 0.
 * Output: best bi-Cayley graph found, as "n m" and edges. "0 0" if none. */

static int d, D;
static int N;
static int T[MAXN * MAXN];
static int INV[MAXN];
static int S[MAXDEG];
static int DIST[MAXV];
static int QUE[MAXV];
static int eof_hit = 0;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int read_long(long *out) {
    int c = getchar();
    while (c != EOF && c != '-' && (c < '0' || c > '9')) c = getchar();
    if (c == EOF) return 0;
    int neg = 0;
    if (c == '-') { neg = 1; c = getchar(); }
    long v = 0;
    while (c >= '0' && c <= '9') { v = v * 10 + (c - '0'); c = getchar(); }
    *out = neg ? -v : v;
    return 1;
}

/* Consumes K pairs. Returns 1 if the table is a valid group with identity 0. */
static int load_group(long n, long K) {
    int ok = (n >= 1 && n <= MAXN && K == n * n);
    for (long i = 0; i < K; i++) {
        long u = 0, v = 0;
        if (!read_long(&u) || !read_long(&v)) { eof_hit = 1; return 0; }
        if (ok) {
            if (u < 0 || u >= n * n || v < 0 || v >= n) ok = 0;
            else T[u] = (int)v;
        }
    }
    if (!ok) return 0;
    N = (int)n;
    for (int j = 0; j < N; j++)
        if (T[j] != j) return 0;
    static unsigned char seen[MAXN];
    for (int x = 0; x < N; x++) {
        memset(seen, 0, (size_t)N);
        for (int y = 0; y < N; y++) {
            int z = T[x * N + y];
            if (seen[z]) return 0;
            seen[z] = 1;
        }
    }
    for (int x = 0; x < N; x++) INV[x] = -1;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (T[x * N + y] == 0) INV[x] = y;
    for (int x = 0; x < N; x++)
        if (INV[x] < 0) return 0;
    return 1;
}

/* Number of vertices within distance D of src in the bi-Cayley graph. */
static int bfs_count(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) DIST[v] = -1;
    int head = 0, tail = 0;
    DIST[src] = 0;
    QUE[tail++] = src;
    while (head < tail) {
        int v = QUE[head++];
        int dv = DIST[v];
        if (dv >= D) continue;
        if (v < N) {
            const int *row = T + v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[S[i]];
                if (DIST[u] < 0) { DIST[u] = dv + 1; QUE[tail++] = u; }
            }
        } else {
            const int *row = T + (v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[INV[S[i]]];
                if (DIST[u] < 0) { DIST[u] = dv + 1; QUE[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Number of (source, vertex) pairs at distance > D, over the two representative sources. */
static int score(void) {
    int V = 2 * N;
    return (V - bfs_count(0)) + (V - bfs_count(N));
}

static int search_group(double until, int *found) {
    long it = 0;
    while (now() < until) {
        for (int i = 0; i < d;) {
            int g = rndint(N), dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == g) { dup = 1; break; }
            if (!dup) S[i++] = g;
        }
        int cur = score();
        int runbest = cur, stall = 0;
        while (cur > 0 && stall < STALL) {
            if ((++it & 255) == 0 && now() > until) break;
            int i = rndint(d);
            int old = S[i];
            int g, dup;
            do {
                g = rndint(N);
                dup = 0;
                for (int j = 0; j < d; j++)
                    if (S[j] == g) { dup = 1; break; }
            } while (dup);
            S[i] = g;
            int nc = score();
            int delta = nc - cur;
            if (delta <= 0 || rnd01() < exp(-delta / TEMP)) {
                cur = nc;
                if (cur < runbest) { runbest = cur; stall = 0; }
                else stall++;
            } else {
                S[i] = old;
                stall++;
            }
        }
        if (cur == 0) {
            memcpy(found, S, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    double tend = t0 + limit - 1.0;

    if (d < 2 || D < 2 || d > MAXDEG) { printf("0 0\n"); return 0; }
    long G = 0, mtot = 0;
    if (!read_long(&G) || !read_long(&mtot)) { printf("0 0\n"); return 0; }

    static int bestN = 0, bestM = 0;
    static int Eu[MAXN * MAXDEG], Ev[MAXN * MAXDEG];
    static int found[MAXDEG];

    for (long g = 0; g < G; g++) {
        long n = 0, K = 0;
        if (!read_long(&n) || !read_long(&K)) break;
        int ok = load_group(n, K);
        if (eof_hit) break;
        if (!ok || N <= d || N <= bestN) continue;
        double left = tend - now();
        if (left <= 0) break;
        double until = now() + left / (double)(G - g);
        if (search_group(until, found)) {
            if (N > bestN) {
                bestN = N;
                bestM = 0;
                for (int x = 0; x < N; x++)
                    for (int i = 0; i < d; i++) {
                        Eu[bestM] = x;
                        Ev[bestM] = N + T[x * N + found[i]];
                        bestM++;
                    }
            }
        }
    }

    if (bestN > 0) {
        printf("%d %d\n", 2 * bestN, bestM);
        for (int e = 0; e < bestM; e++) printf("%d %d\n", Eu[e], Ev[e]);
    } else {
        printf("0 0\n");
    }
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

    Returns None if no sign convention verifies with lib.is_valid.
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


# ------------------------------------------------------------ group tables

def _canon(T, e):
    """Relabel a group table so that its identity (old index e) becomes index 0."""
    N = T.shape[0]
    perm = np.arange(N, dtype=np.int64)
    perm[0], perm[e] = e, 0
    T2 = perm[T[np.ix_(perm, perm)]]
    if not (np.array_equal(T2[0], np.arange(N)) and np.array_equal(T2[:, 0], np.arange(N))):
        return None
    return T2


def _mat_group(q, special):
    """GL(2,q) (special=False) or SL(2,q) (special=True) as a table with identity at 0, or None."""
    F = lib.GF(q)
    M, A = F.mul_table, F.add_table
    q2, q3 = q * q, q * q * q
    keys = np.arange(q ** 4, dtype=np.int64)
    a = keys // q3
    b = (keys // q2) % q
    c = (keys // q) % q
    dd = keys % q
    negv = np.array([F.neg(x) for x in range(q)], dtype=np.int64)
    det = A[M[a, dd], negv[M[b, c]]]
    mask = (det == 1) if special else (det != 0)
    E = keys[mask]
    N = int(E.size)
    idx = np.full(q ** 4, -1, dtype=np.int64)
    idx[E] = np.arange(N, dtype=np.int64)
    a, b, c, dd = a[mask], b[mask], c[mask], dd[mask]
    a1, b1, c1, d1 = a[:, None], b[:, None], c[:, None], dd[:, None]
    a2, b2, c2, d2 = a[None, :], b[None, :], c[None, :], dd[None, :]
    r00 = A[M[a1, a2], M[b1, c2]]
    r01 = A[M[a1, b2], M[b1, d2]]
    r10 = A[M[c1, a2], M[d1, c2]]
    r11 = A[M[c1, b2], M[d1, d2]]
    T = idx[r00 * q3 + r01 * q2 + r10 * q + r11]
    if T.min() < 0:
        return None
    e = int(idx[q3 + 1])
    return _canon(T, e)


def _times_cyclic(T, k):
    """Direct product of a table (identity 0) with Z_k; identity stays 0."""
    N0 = T.shape[0]
    zc = (np.arange(k)[:, None] + np.arange(k)[None, :]) % k
    t4 = T[:, None, :, None] * k + zc[None, :, None, :]
    return t4.reshape(N0 * k, N0 * k)


def _metacyclic(m, k, r):
    """Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e)."""
    N = m * k
    i = np.arange(N, dtype=np.int64)
    a, b = i // k, i % k
    rp = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    a1, b1 = a[:, None], b[:, None]
    a2, b2 = a[None, :], b[None, :]
    na = (a1 + rp[b1] * a2) % m
    nb = (b1 + b2) % k
    return na * k + nb


def _specs(lo, hi, rng):
    fixed = []
    bases = [("GL23", 3, False), ("SL23", 3, True), ("SL25", 5, True), ("GL25", 5, False),
             ("GL24", 4, False), ("SL27", 7, True), ("SL28", 8, True), ("SL29", 9, True)]
    for label, q, special in bases:
        nb = q * (q * q - 1) if special else (q * q - 1) * (q * q - q)
        for k in range(1, hi // nb + 1):
            N = nb * k
            if lo <= N <= hi:
                fixed.append((N, "mat", (q, special, k), label))
    meta = []
    for m in range(3, hi // 2 + 1):
        for k in range(2, hi // m + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            cands = [r for r in range(2, m) if gcd(r, m) == 1 and pow(r, k, m) == 1]
            for r in rng.sample(cands, min(3, len(cands))):
                meta.append((N, "meta", (m, k, r), ("meta", m, k)))
    return fixed, meta


def _build_table(kind, params):
    if kind == "mat":
        q, special, k = params
        T = _mat_group(q, special)
        if T is None:
            return None
        return T if k == 1 else _times_cyclic(T, k)
    m, k, r = params
    return _metacyclic(m, k, r)


def _choose_groups(d, D, n_have, moore, rng):
    lo = max(n_have, RECORDS.get((d, D), 0)) // 2 + 1
    hi = min(moore // 2, MAX_TABLE)
    if hi < max(lo, d + 2):
        return []
    fixed, meta = _specs(lo, hi, rng)
    fixed.sort(key=lambda s: s[0])
    rng.shuffle(meta)
    pool = []
    for i in range(max(len(fixed), len(meta))):
        if i < len(fixed):
            pool.append(fixed[i])
        if i < len(meta):
            pool.append(meta[i])
    chosen, pairs, per_label = [], 0, {}
    for N, kind, params, label in pool:
        if len(chosen) >= MAX_GROUPS:
            break
        if per_label.get(label, 0) >= 2 or N < d + 2:
            continue
        if pairs + N * N > MAX_PAIRS:
            continue
        T = _build_table(kind, params)
        if T is None or int(T.shape[0]) != N:
            continue
        chosen.append(T)
        pairs += N * N
        per_label[label] = per_label.get(label, 0) + 1
    return chosen


# ------------------------------------------------------------------- build

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
    if d > 12 or best[0] >= moore:
        return best

    try:
        groups = _choose_groups(d, D, best[0], moore, random.Random(seed))
    except Exception:
        return best
    if not groups:
        return best

    edges = []
    for T in groups:
        N = int(T.shape[0])
        edges.append((N, N * N))
        edges.extend(zip(range(N * N), T.ravel().tolist()))

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 4.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(len(groups), edges), timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
