"""Bi-Cayley lift search over semidirect products Z_m x| Z_k (single orbit, degree d).

Vertices: A_g = g and B_h = G + h for g, h in G, with edges A_g ~ B_{g*s} for s in S (|S| = d).
Left multiplication is an automorphism that is transitive on each side, so diameter <= D
reduces to two BFS runs (from A_e and from B_e). The C engine searches S by simulated
annealing on the number of unreached pairs, with targeted moves toward unreached vertices.
A ratchet on the group order keeps the largest success. Each graph is checked with lib.is_valid.
K_{d,d} (or PG / Araujo-Lopez / generalized quadrangle constructions) is the fallback.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley single-orbit search over G = Z_M x| Z_K with r^K = 1 mod M.
 * Usage: prog d D seed time_limit M K R
 * Output: "1 s_1 ... s_d" when a valid connection set S is found, else "0".
 * Graph: A_g ~ B_{g*s} for s in S; valid iff every A-node and B-node is within
 * distance D of A_e (A-A, A-B pairs) and every B-node is within D of B_e (B-B pairs).
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 8192
#define MAXDEG 32
#define MAXK 256
#define TEMP 0.6
#define PATIENCE 40000

static int d, D, M, K, R, G;
static int PW[MAXK];
static int S[MAXDEG];
static int TA[MAXDEG][MAXG];
static int TB[MAXDEG][MAXG];
static int dist[2 * MAXG];
static int qu[2 * MAXG];
static int unA[MAXG], curUnA[MAXG];
static int curN = 0, nun = 0;
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

static int gmul(int x, int y) {
    int a = x / K, b = x % K, c = y / K, e = y % K;
    long t = ((long)a + (long)PW[b] * c) % M;
    return (int)(t * K + (b + e) % K);
}

static int ginv(int x) {
    int a = x / K, b = x % K;
    int nb = (K - b) % K;
    long t = ((long)PW[nb] * a) % M;
    long na = (M - t) % M;
    return (int)(na * K + nb);
}

static void setcol(int i, int s) {
    S[i] = s;
    int si = ginv(s);
    for (int g = 0; g < G; g++) {
        TA[i][g] = gmul(g, s);
        TB[i][g] = gmul(g, si);
    }
}

/* BFS from src up to depth D; returns number of nodes reached (queue length). */
static int bfs(int src) {
    int N2 = 2 * G;
    for (int i = 0; i < N2; i++) dist[i] = -1;
    int head = 0, tail = 0;
    dist[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        int dv = dist[v];
        if (dv >= D) continue;
        if (v < G) {
            for (int i = 0; i < d; i++) {
                int u = G + TA[i][v];
                if (dist[u] < 0) {
                    dist[u] = dv + 1;
                    qu[tail++] = u;
                }
            }
        } else {
            int h = v - G;
            for (int i = 0; i < d; i++) {
                int u = TB[i][h];
                if (dist[u] < 0) {
                    dist[u] = dv + 1;
                    qu[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Number of unreached (node, source) combinations; fills unA with unreached A-nodes from A_e. */
static int cost(void) {
    int tail = bfs(0);
    int c1 = 2 * G - tail;
    nun = 0;
    for (int g = 0; g < G; g++)
        if (dist[g] < 0) unA[nun++] = g;
    int tail2 = bfs(G);
    int cb = 0;
    for (int k = 0; k < tail2; k++)
        if (qu[k] >= G) cb++;
    return c1 + (G - cb);
}

static void save_cur(void) {
    curN = nun;
    memcpy(curUnA, unA, sizeof(int) * (size_t)nun);
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    M = atoi(argv[5]);
    K = atoi(argv[6]);
    R = atoi(argv[7]);
    G = M * K;
    if (d < 1 || d > MAXDEG || D < 2 || M < 2 || K < 1 || K > MAXK || G > MAXG || G < d) {
        printf("0\n");
        return 0;
    }
    R %= M;
    if (R < 0) R += M;
    PW[0] = 1 % M;
    for (int b = 1; b < K; b++) PW[b] = (int)(((long)PW[b - 1] * R) % M);
    if ((((long)PW[K - 1]) * R) % M != 1 % M) {
        printf("0\n");
        return 0;
    }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    double t_end = now() + tl;
    int found = 0;
    long checks = 0;
    while (!found && now() < t_end) {
        int cnt = 0;
        while (cnt < d) {
            int x = rndint(G), dup = 0;
            for (int j = 0; j < cnt; j++)
                if (S[j] == x) {
                    dup = 1;
                    break;
                }
            if (!dup) {
                setcol(cnt, x);
                cnt++;
            }
        }
        int cur = cost();
        save_cur();
        int best = cur;
        long since = 0;
        while (cur > 0) {
            if ((++checks & 127) == 0 && now() > t_end) break;
            if (since > PATIENCE) break;
            int i = rndint(d);
            int old = S[i];
            int nv;
            if (curN > 0 && rnd01() < 0.5) {
                int h = curUnA[rndint(curN)];
                int j = rndint(d);
                nv = gmul(ginv(h), S[j]);
            } else {
                nv = rndint(G);
            }
            if (nv == old) {
                since++;
                continue;
            }
            int dup = 0;
            for (int j = 0; j < d; j++)
                if (S[j] == nv) {
                    dup = 1;
                    break;
                }
            if (dup) {
                since++;
                continue;
            }
            setcol(i, nv);
            int c2 = cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / TEMP)) {
                cur = c2;
                save_cur();
                if (cur < best) {
                    best = cur;
                    since = 0;
                } else {
                    since++;
                }
            } else {
                setcol(i, old);
                since++;
            }
        }
        if (cur == 0) found = 1;
    }

    if (found) {
        printf("1");
        for (int i = 0; i < d; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions (kept as strong fallbacks for D = 3 and D = 4).
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


def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but fall back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley search over semidirect products.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k, r) for Z_m x| Z_k with m*k >= target, or None."""
    for _ in range(200):
        k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k))
        if k == 1:
            r = 1
        elif k == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k, r
    return None


def _bc_call(d, D, seed, tl, m, k, r):
    """Run the C search for connection set S; return a list of d elements or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(tl, 2), m, k, r], timeout=tl + 8.0)
    except Exception:
        return None
    tok = out.split()
    if len(tok) < d + 1 or tok[0] != "1":
        return None
    try:
        return [int(x) for x in tok[1:1 + d]]
    except ValueError:
        return None


def _bicayley_graph(m, k, r, S):
    """Bi-Cayley graph: A_g ~ B_{g*s} for s in S, with g*s in Z_m x| Z_k (element (a,b) = a*k+b)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    edges = []
    for s in S:
        sa, sb = divmod(int(s), k)
        img = ((a + pw[b] * sa) % m) * k + (b + sb) % k
        edges.extend(zip(range(G), (G + img).tolist()))
    return 2 * G, edges


def _bicayley_search(d, D, rng, final, floor_n):
    """Ratchet the group order upward; return the largest validated (n, edges) with n > floor_n, or None."""
    bestG = floor_n // 2  # any success with G > bestG gives 2G > floor_n
    best = None
    step = max(1, bestG // 50)
    goal = bestG + 1 + step
    while True:
        remaining = final - time.monotonic()
        if remaining < 1.5:
            break
        g = _sample_group(goal, rng)
        if g is None:
            goal += 1
            continue
        m, k, r = g
        G = m * k
        tl = min(remaining - 0.5, 4.0)
        S = _bc_call(d, D, rng.randrange(1 << 30), tl, m, k, r)
        if S is None:
            # Ease the goal back toward the best order found so far.
            goal = bestG + 1 + max(0, (goal - bestG - 1) // 2)
            continue
        n, edges = _bicayley_graph(m, k, r, S)
        if lib.is_valid(n, edges, d, D) and n > 2 * bestG:
            best = (n, edges)
            bestG = G
            step = max(1, bestG // 50)
        goal = bestG + 1 + step
    return best


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.88 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            an, ae = lib.araujo_lopez_graph(d - 2)
            sn, se = _safe_saturate(an, ae, d, D)
            consider(sn, se)
            consider(an, ae)
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: bi-Cayley single-orbit search, ratcheting the order upward.
    if D >= 3 and d >= 3 and time.monotonic() < final - 2.0:
        try:
            res = _bicayley_search(d, D, rng, final, best_n)
            if res is not None and res[0] > best_n:
                best = res
                best_n = res[0]
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
