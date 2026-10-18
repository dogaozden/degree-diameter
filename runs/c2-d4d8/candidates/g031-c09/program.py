"""Bi-Cayley generating-set search over metacyclic groups (replaces the voltage-dart search).

Construction: vertices A = G and B = G for a group G = Z_m x|_r Z_k of order N, with
A_x ~ B_{x*s} for s in S, |S| = d. Left multiplication is a regular automorphism on each side,
so the diameter is at most D iff BFS from A_e and from B_e reaches everything within D. The
search picks the generating set S directly: random start, then annealing where each move samples
several replacement elements and keeps the one with the fewest unreached pairs. Orders climb from
the current best. The record order is tried directly when it is above the current order.

Python builds algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}), checks them with
lib.is_valid, and only accepts the C output if it is valid and strictly larger.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 3400
#define MAXV (2 * MAXN)
#define MAXD 16

static int d, D;
static long MOORE;
static double t_end;
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
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int N;
static int Gm, Gk, Gr;
static int rp[MAXN];

static void set_group(int m, int k, int r) {
    Gm = m; Gk = k; Gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}
static int gmul(int x, int y) {
    int a = x / Gk, b = x % Gk, c = y / Gk, e = y % Gk;
    int ac = (int)(((long)a + (long)rp[b] * c) % Gm);
    return ac * Gk + (b + e) % Gk;
}
static int ginv(int x) {
    int a = x / Gk, b = x % Gk;
    int nb = (Gk - b) % Gk;
    long ia = ((long)Gm - (long)rp[nb] * a % Gm) % Gm;
    return (int)ia * Gk + nb;
}

/* Uniform random metacyclic group of order n (reservoir over all valid (m, r)). */
static int pick_group(int n, int *om, int *ok, int *orr) {
    long cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { *om = 1; *ok = k; *orr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return cnt > 0;
}

static int Sg[MAXD], Si[MAXD];
static int mark[MAXV], lvl[MAXV], qb[MAXV];
static int stamp = 0;

/* BFS from src within depth D on the bipartite graph A_x ~ B_{x s}; returns reached count. */
static long reached_from(int src) {
    stamp++;
    int head = 0, tail = 0;
    qb[tail++] = src;
    mark[src] = stamp;
    lvl[src] = 0;
    while (head < tail) {
        int v = qb[head++];
        if (lvl[v] >= D) continue;
        int nl = lvl[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + gmul(v, Sg[i]);
                if (mark[u] != stamp) {
                    mark[u] = stamp;
                    lvl[u] = nl;
                    qb[tail++] = u;
                }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = gmul(y, Si[i]);
                if (mark[u] != stamp) {
                    mark[u] = stamp;
                    lvl[u] = nl;
                    qb[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static long eval_bad(void) {
    long a = 2L * N - reached_from(0);
    long b = 2L * N - reached_from(N);
    return a + b;
}

static int have = 0;
static int bN, bm, bk, br;
static int bS[MAXD];

static int attempt(int n, double until) {
    if (n < d) return 0;
    N = n;
    while (now() < until) {
        int m, k, r;
        if (!pick_group(n, &m, &k, &r)) return 0;
        set_group(m, k, r);
        for (int i = 0; i < d; i++) {
            int x, dup;
            do {
                x = rndint(N);
                dup = 0;
                for (int j = 0; j < i; j++)
                    if (Sg[j] == x) dup = 1;
            } while (dup);
            Sg[i] = x;
            Si[i] = ginv(x);
        }
        long bad = eval_bad();
        double T = 1.0;
        for (int it = 0; it < 6000 && bad > 0; it++) {
            if ((it & 127) == 0 && now() > until) break;
            int i = rndint(d);
            int old = Sg[i], oldi = Si[i];
            int bx = -1, bi = -1;
            long bnb = 0;
            for (int c = 0; c < 4; c++) {
                int x = rndint(N), dup = 0;
                for (int j = 0; j < d; j++)
                    if (j != i && Sg[j] == x) dup = 1;
                if (dup) continue;
                Sg[i] = x;
                Si[i] = ginv(x);
                long nb = eval_bad();
                if (bx < 0 || nb < bnb) { bx = x; bi = Si[i]; bnb = nb; }
            }
            Sg[i] = old;
            Si[i] = oldi;
            if (bx < 0) continue;
            if (bnb <= bad || rnd01() < exp((double)(bad - bnb) / T)) {
                Sg[i] = bx;
                Si[i] = bi;
                bad = bnb;
            }
            T *= 0.999;
            if (T < 0.02) T = 1.0;
        }
        if (bad == 0) {
            have = 1;
            bN = N; bm = m; bk = k; br = r;
            memcpy(bS, Sg, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit lo target\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]);
    long target = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound();
    long NMAX = MOORE / 2;
    if (NMAX > MAXN) NMAX = MAXN;
    if (lo < d) lo = d;

    long step = 1;
    while (now() < t_end && lo < NMAX) {
        int use_t = (target > lo && target <= NMAX) && rndint(2) == 0;
        long cand = use_t ? target : lo + step;
        if (cand > NMAX) cand = NMAX;
        if (cand <= lo) break;
        double left = t_end - now();
        double sl = left / 6.0;
        if (sl < 0.5) sl = 0.5;
        if (sl > 6.0) sl = 6.0;
        if (sl > left) sl = left;
        if (attempt((int)cand, now() + sl)) {
            lo = cand;
            if (!use_t && step < 512) step *= 2;
        } else if (!use_t && step > 1) {
            step /= 2;
        }
    }

    if (have) {
        set_group(bm, bk, br);
        printf("%d %d\n", 2 * bN, bN * d);
        for (int x = 0; x < bN; x++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", x, bN + gmul(x, bS[i]));
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''

# Best known orders (used to set the record target for the C search).
RECORDS = {(3, 3): 14, (4, 8): 2184}


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 0.5:
        return best

    record = RECORDS.get((d, D), 0)
    lo = best[0] // 2
    target = record // 2
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, lo, target],
                         stdin_graph=None, timeout=budget + 3)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
