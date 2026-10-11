"""Haar-graph difference-cover search for D = 3.

For |S| = d and m with S - S = Z_m, the Haar graph H(Z_m, S) (2m vertices, d-regular,
bipartite) has diameter <= 3. A C annealer searches for such covers with m large enough to
beat the current best order. Fallbacks: the projective-plane / Araujo-Lopez starts and the
conic blow-up, then K_{d,d}. Every returned graph is checked with lib.is_valid.
"""
import time

import lib

DIFF_C = r'''
/* Find S subset of Z_m, |S| = k, 0 in S, with every nonzero residue a difference s - t.
 * Usage: prog m k seed time_limit
 * stdout: "FOUND" then the k elements, or "NONE".
 * Simulated annealing on the number of uncovered differences.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int m, k;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];   /* cnt[x] = number of ordered pairs (s, t), s != t in S, s - t = x */
static int cost;        /* number of x in 1..m-1 with cnt[x] == 0 */

static int md(int x) { x %= m; return x < 0 ? x + m : x; }
static void dec(int x) { if (--cnt[x] == 0) cost++; }
static void inc(int x) { if (cnt[x]++ == 0) cost--; }

/* Remove S[i] (its value stays in S[i] until replaced). */
static void remove_at(int i) {
    int s = S[i];
    for (int j = 0; j < k; j++)
        if (j != i) { dec(md(s - S[j])); dec(md(S[j] - s)); }
    inS[s] = 0;
}

/* Put y in slot i. */
static void add_at(int i, int y) {
    for (int j = 0; j < k; j++)
        if (j != i) { inc(md(y - S[j])); inc(md(S[j] - y)); }
    S[i] = y;
    inS[y] = 1;
}

static void randomize(void) {
    for (int x = 0; x < m; x++) { cnt[x] = 0; inS[x] = 0; }
    cost = m - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < k; i++) {
        int y;
        do y = rndint(m); while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    for (int i = 0; i < k; i++)
        for (int j = i + 1; j < k; j++) {
            inc(md(S[i] - S[j]));
            inc(md(S[j] - S[i]));
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s m k seed time_limit\n", argv[0]);
        return 2;
    }
    m = atoi(argv[1]);
    k = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (m < 2 || m > MAXM || k < 2 || k > MAXK || k > m || (long)k * (k - 1) < m - 1) {
        printf("NONE\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + limit * 0.9;
    randomize();
    long it = 0, last_imp = 0;
    int bestc = cost;
    const double T = 0.45;

    while (cost > 0) {
        if ((++it & 1023) == 0 && now() > tend) break;
        if (cost < bestc) { bestc = cost; last_imp = it; }
        if (it - last_imp > 3000000) {       /* stagnation: restart */
            randomize();
            bestc = cost;
            last_imp = it;
            continue;
        }
        int i = 1 + rndint(k - 1);           /* slot 0 stays 0 (translation invariance) */
        int old = S[i];
        int y;
        if (rnd01() < 0.8) {
            /* aim at an uncovered difference x: new element = S[j] + x */
            int x, tries = 0;
            do { x = 1 + rndint(m - 1); } while (cnt[x] != 0 && ++tries < 64);
            int j = rndint(k);
            y = md(S[j] + x);
        } else {
            y = rndint(m);
        }
        if (inS[y]) continue;
        int pre = cost;
        remove_at(i);
        add_at(i, y);
        int delta = cost - pre;
        if (delta <= 0 || rnd01() < exp(-delta / T)) continue;
        remove_at(i);
        add_at(i, old);
    }

    if (cost == 0) {
        printf("FOUND\n");
        for (int i = 0; i < k; i++) printf("%d ", S[i]);
        printf("\n");
    } else {
        printf("NONE\n");
    }
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, with a conic and a dual conic (order 2(q^2+q+1)+2(q+1))."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)  # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    """Structured start graphs (validity checked by the caller)."""
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    return out


def difference_cover(m, k, seed, budget):
    """Return a list S of k residues mod m with S - S = Z_m, or None."""
    text = lib.run_c(DIFF_C, [m, k, seed, f"{budget:.2f}"], timeout=budget + 5)
    toks = text.split()
    if len(toks) < 1 + k or toks[0] != "FOUND":
        return None
    S = [int(x) for x in toks[1:1 + k]]
    if len(set(x % m for x in S)) != k:
        return None
    return S


def haar_search(d, D, seed, lo_n, deadline):
    """Best Haar graph H(Z_m, S), |S| = d, S - S = Z_m, with 2m > lo_n. Returns (n, edges) or None."""
    if D != 3 or d < 3:
        return None
    best = None
    m = lo_n // 2 + 1
    m_hi = d * (d - 1) + 1          # a cover of Z_m by d-1 nonzero differences needs m <= d(d-1)+1
    fails = 0
    while m <= m_hi and fails < 2:
        left = deadline - time.monotonic()
        if left < 1.5:
            break
        budget = min(left, max(3.0, left / 3))
        S = difference_cover(m, d, seed * 1000 + m, budget)
        if S is None:
            fails += 1
        else:
            fails = 0
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
        m += 1
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit - 1.0

    start = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (start is None or cand[0] > start[0]):
            start = cand

    if start is not None:
        best = start
    else:
        best = lib.haar_graph(d, range(d))          # K_{d,d}
        if not lib.is_valid(best[0], best[1], d, D):
            best = (2, [(0, 1)])                    # always valid for d, D >= 1

    try:
        res = haar_search(d, D, seed, best[0], deadline)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
    except Exception:
        pass   # keep the valid structured fallback

    return best
