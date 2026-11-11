"""Group-Cayley search program.

Changed in this version: for D >= 2 the C engine no longer hill-climbs lifts. It searches bipartite
Cayley graphs instead. A group G of order N gives the graph on 2N vertices a_x, b_y, with a_x adjacent
to b_{x*s} for s in S, where |S| = d. Left multiplication is an automorphism, so the diameter check
needs only BFS from a_e and b_e. Groups come from PSL/SL(2,q), direct products with cyclic groups,
and a few metacyclic semidirect products. Graph search is on the group multiplication table, which
Python passes to C. The algebraic starts (projective planes, W(q), H(3)) remain the fallback, and
every candidate is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite Cayley search over supplied finite groups.
 * Usage: prog d D seed time_limit   (stdin: "n m" then m lines of 2 ints = a flat int stream)
 * Flat stream: ng, then for each group: N, then N*N mul table entries (identity must be index 0).
 * Output: "n m" then the edges of the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 64

typedef struct { int N; int *mul; int *inv; } Grp;

static int d, D;
static int *distv, *queue_buf;
static int inv_s[MAXD];
static int S_found[MAXD], best_S[MAXD];

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

/* Number of unreached (source, vertex) pairs within distance D, sources a_e and b_e. */
static long eval_bad(const Grp *G, const int *S) {
    int N = G->N, n2 = 2 * N;
    for (int k = 0; k < d; k++) inv_s[k] = G->inv[S[k]];
    long bad = 0;
    for (int src = 0; src < 2; src++) {
        for (int v = 0; v < n2; v++) distv[v] = -1;
        int head = 0, tail = 0;
        int s0 = src ? N : 0;
        distv[s0] = 0;
        queue_buf[tail++] = s0;
        while (head < tail) {
            int v = queue_buf[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < N) {
                const int *row = G->mul + (size_t)v * N;
                for (int k = 0; k < d; k++) {
                    int u = N + row[S[k]];
                    if (distv[u] < 0) { distv[u] = dv + 1; queue_buf[tail++] = u; }
                }
            } else {
                const int *row = G->mul + (size_t)(v - N) * N;
                for (int k = 0; k < d; k++) {
                    int u = row[inv_s[k]];
                    if (distv[u] < 0) { distv[u] = dv + 1; queue_buf[tail++] = u; }
                }
            }
        }
        bad += n2 - tail;
    }
    return bad;
}

static int try_group(const Grp *G, double until) {
    int N = G->N;
    int S[MAXD];
    while (now() < until) {
        for (int k = 0; k < d; k++) {
            int e, ok;
            do {
                e = rndint(N);
                ok = 1;
                for (int j = 0; j < k; j++)
                    if (S[j] == e) { ok = 0; break; }
            } while (!ok);
            S[k] = e;
        }
        long bad = eval_bad(G, S), bestbad = bad;
        long stall = 0, step = 0;
        while (bad > 0 && stall < 300000) {
            if ((++step & 1023) == 0 && now() > until) return 0;
            int k = rndint(d), e = rndint(N), ok = 1;
            for (int j = 0; j < d; j++)
                if (S[j] == e) { ok = 0; break; }
            if (!ok) continue;
            int old = S[k];
            S[k] = e;
            long nb = eval_bad(G, S);
            if (nb <= bad || rnd01() < 0.02) {
                bad = nb;
                if (bad < bestbad) { bestbad = bad; stall = 0; }
                else stall++;
            } else {
                S[k] = old;
                stall++;
            }
        }
        if (bad == 0) {
            memcpy(S_found, S, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < stream\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t_end = now() + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n0, m0;
    if (d < 1 || d > MAXD || D < 1 || scanf("%d %d", &n0, &m0) != 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    size_t total = 2 * (size_t)m0;
    int *flat = malloc(sizeof(int) * (total + 2));
    for (size_t i = 0; i < total; i++) {
        if (scanf("%d", &flat[i]) != 1) { printf("0 0\n"); return 0; }
    }
    if (total == 0) { printf("0 0\n"); return 0; }

    int ng = flat[0];
    size_t pos = 1;
    Grp *grp = calloc(ng > 0 ? ng : 1, sizeof(Grp));
    int maxN = 1, cnt_g = 0;
    for (int g = 0; g < ng; g++) {
        if (pos >= total) break;
        int N = flat[pos++];
        if (N < 1 || pos + (size_t)N * N > total) break;
        grp[cnt_g].N = N;
        grp[cnt_g].mul = malloc(sizeof(int) * (size_t)N * N);
        memcpy(grp[cnt_g].mul, flat + pos, sizeof(int) * (size_t)N * N);
        pos += (size_t)N * N;
        grp[cnt_g].inv = malloc(sizeof(int) * N);
        int okg = 1;
        for (int x = 0; x < N && okg; x++) {
            int found = -1;
            for (int y = 0; y < N; y++)
                if (grp[cnt_g].mul[(size_t)x * N + y] == 0) { found = y; break; }
            if (found < 0) okg = 0;
            grp[cnt_g].inv[x] = found;
        }
        if (!okg || grp[cnt_g].mul[0] != 0) { free(grp[cnt_g].mul); free(grp[cnt_g].inv); continue; }
        if (N > maxN) maxN = N;
        cnt_g++;
    }
    ng = cnt_g;
    distv = malloc(sizeof(int) * 2 * (size_t)maxN);
    queue_buf = malloc(sizeof(int) * 2 * (size_t)maxN);

    int best_n = 0, best_g = -1;
    for (int g = 0; g < ng; g++) {
        int N = grp[g].N;
        if (2L * N <= best_n || N < d) continue;
        int cnt = 0;
        for (int j = g; j < ng; j++)
            if (2L * grp[j].N > best_n && grp[j].N >= d) cnt++;
        double left = t_end - now();
        if (left <= 0) break;
        double until = now() + left / cnt;
        if (try_group(&grp[g], until)) {
            best_n = 2 * N;
            best_g = g;
            memcpy(best_S, S_found, sizeof(int) * d);
        }
    }

    if (best_g < 0) {
        printf("0 0\n");
        return 0;
    }
    Grp *G = &grp[best_g];
    int N = G->N;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++) {
            int y = G->mul[(size_t)x * N + best_S[k]];
            printf("%d %d\n", x, N + y);
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Both sign conventions are tried, and the result is accepted only if lib.is_valid confirms
    it. Returns (n, edges) or None.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
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
    return out


def _ord_sl(q, psl):
    o = q * (q * q - 1)
    return o // 2 if (psl and q % 2 == 1) else o


def _sl2(q, psl):
    """Multiplication table (identity = index 0) of SL(2,q), or PSL(2,q) = SL/{+-I} when psl."""
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    neg = [F.neg(x) for x in range(q)]

    def canon(X):
        if not psl:
            return X
        Y = (neg[X[0]], neg[X[1]], neg[X[2]], neg[X[3]])
        return min(X, Y)

    I = (1, 0, 0, 1)
    keys = set()
    for a, b, c, e in itertools.product(range(q), repeat=4):
        if A[M[a][e]][neg[M[b][c]]] == 1:
            keys.add(canon((a, b, c, e)))
    keys.discard(canon(I))
    elems = [canon(I)] + sorted(keys)
    idx = {X: i for i, X in enumerate(elems)}
    table = []
    for X in elems:
        a, b, c, e = X
        row = []
        for Y in elems:
            p, r, s, t = Y
            row.append(idx[canon((A[M[a][p]][M[b][s]], A[M[a][r]][M[b][t]],
                                  A[M[c][p]][M[e][s]], A[M[c][r]][M[e][t]]))])
        table.append(row)
    return len(elems), table


def _direct_cyclic(N, table, k):
    """Table of G x Z_k; element g*k + c, identity index 0."""
    rows = []
    for g in range(N):
        for c in range(k):
            row = []
            for h in range(N):
                gh = table[g][h]
                for c2 in range(k):
                    row.append(gh * k + (c + c2) % k)
            rows.append(row)
    return N * k, rows


def _metacyclic_candidates(lo, hi, rng, count):
    cands = []
    trials = 0
    while len(cands) < count and trials < 300:
        trials += 1
        N = rng.randint(lo, hi)
        divs = [k for k in range(2, N) if N % k == 0]
        if not divs:
            continue
        k = rng.choice(divs)
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            cands.append((m, k, rng.choice(rs)))
    return cands


def _group_pool(lo, hi, seed):
    """Return [(N, table)] for groups with lo <= N <= hi, largest first."""
    rng = random.Random(seed)
    cache = {}

    def base(q, psl):
        if (q, psl) not in cache:
            cache[(q, psl)] = _sl2(q, psl)
        return cache[(q, psl)]

    out = []
    specs = [(8, True, 1), (11, True, 1), (9, False, 1), (7, False, 1),
             (7, True, 3), (7, True, 4), (7, False, 2)]
    for q, psl, k in specs:
        if lo <= _ord_sl(q, psl) * k <= hi:
            N, table = base(q, psl)
            if k > 1:
                N, table = _direct_cyclic(N, table, k)
            out.append((N, table))
    for m, k, r in _metacyclic_candidates(lo, hi, rng, 3):
        n, mulf, _ = lib.semidirect_group(m, k, r)
        out.append((n, [[mulf(x, y) for y in range(n)] for x in range(n)]))
    out.sort(key=lambda t: -t[0])
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

    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and hexg[0] > best[0] and lib.is_valid(hexg[0], hexg[1], d, D):
            best = hexg

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    lo = best[0] // 2 + 1
    hi = min(moore // 2, 800)
    if lo > hi:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        groups = _group_pool(lo, hi, seed)
        if groups:
            flat = [len(groups)]
            for N, table in groups:
                flat.append(N)
                flat.extend(v for row in table for v in row)
            if len(flat) % 2:
                flat.append(0)
            edges = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=(1, edges), timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
    except Exception:
        pass
    return best
