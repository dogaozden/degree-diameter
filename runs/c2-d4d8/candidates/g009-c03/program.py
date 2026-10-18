"""Haar bi-Cayley search with exhaustive connection-set enumeration.

Construction: the bipartite Haar graph of the cyclic group Z_N with connection set S of size d,
with A_i ~ B_{i+s} for s in S. The group acts regularly on each side, so the diameter is at most D
iff BFS from A_0 and from B_0 reaches every vertex within D. Each check is O(N*d) with no
adjacency array. WLOG 0, 1 in S (translation and unit scaling), so for d = 4 the search is over
all pairs {b, c}, which is about N^2/2 sets and runs exhaustively for N near 1100.

Strategy: jump straight to the record order per side, N = record/2 + 1, using 60% of the search
slice. If that fails, climb from the current best one N at a time. Random sampling is used for
d >= 5. Python keeps the algebraic start as a fallback and only accepts a C result that is
valid and strictly larger.
"""
import time

import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXE 65536

static int d, D;
static long MOORE;
static long target_n = 0;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

static int seen_st[2 * MAXN];
static int dist_[2 * MAXN];
static int qb[2 * MAXN];
static int stamp_c = 0;
static int vals[MAXN];
static int have_haar = 0, HN = 0, HS[MAXD];

/* Vertices A_i = i, B_j = N + j. Edges A_i - B_{i+s}, for s in S. */
static int reach_all(int src, const int *S, int N) {
    stamp_c++;
    int head = 0, tail = 0;
    qb[tail++] = src;
    seen_st[src] = stamp_c;
    dist_[src] = 0;
    while (head < tail) {
        int v = qb[head++];
        if (dist_[v] >= D) continue;
        int nd = dist_[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + (v + S[i]) % N;
                if (seen_st[u] != stamp_c) {
                    seen_st[u] = stamp_c;
                    dist_[u] = nd;
                    qb[tail++] = u;
                }
            }
        } else {
            int j = v - N;
            for (int i = 0; i < d; i++) {
                int u = (j - S[i] + N) % N;
                if (seen_st[u] != stamp_c) {
                    seen_st[u] = stamp_c;
                    dist_[u] = nd;
                    qb[tail++] = u;
                }
            }
        }
    }
    return tail == 2 * N;
}

/* Left translation is an automorphism that is transitive on each side. */
static int ok_set(int N, const int *S) {
    return reach_all(0, S, N) && reach_all(N, S, N);
}

static void save_set(int N, const int *S) {
    have_haar = 1;
    HN = N;
    for (int i = 0; i < d; i++) HS[i] = S[i];
}

/* Search for a Haar graph of Z_N with d-element S containing {0, 1}. Sets *complete = 1 when the
 * whole family was tried without success. Returns 1 on success (the set is saved). */
static int try_N(int N, double until, int *complete) {
    *complete = 0;
    int k = d - 2;
    if (N < d || N > MAXN / 2 || 2L * N > MOORE) return 0;
    int M = N - 2;
    if (M < k) { *complete = 1; return 0; }
    for (int i = 0; i < M; i++) vals[i] = i + 2;
    for (int i = M - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = vals[i]; vals[i] = vals[j]; vals[j] = t;
    }
    int S[MAXD];
    S[0] = 0;
    S[1] = 1;
    if (k == 0) {
        *complete = 1;
        if (ok_set(N, S)) { save_set(N, S); return 1; }
        return 0;
    }
    long cnt = 0;
    if (k == 1) {
        for (int a = 0; a < M; a++) {
            if ((++cnt & 255) == 0 && now() > until) return 0;
            S[2] = vals[a];
            if (ok_set(N, S)) { save_set(N, S); return 1; }
        }
        *complete = 1;
        return 0;
    }
    if (k == 2) {
        for (int a = 0; a < M; a++) {
            for (int b = a + 1; b < M; b++) {
                if ((++cnt & 255) == 0 && now() > until) return 0;
                S[2] = vals[a];
                S[3] = vals[b];
                if (ok_set(N, S)) { save_set(N, S); return 1; }
            }
        }
        *complete = 1;
        return 0;
    }
    for (;;) {
        if ((++cnt & 15) == 0 && now() > until) return 0;
        for (int i = 0; i < k; i++) {
            int r, dup;
            do {
                r = rndint(M);
                dup = 0;
                for (int j = 0; j < i; j++)
                    if (vals[r] == S[2 + j]) dup = 1;
            } while (dup);
            S[2 + i] = vals[r];
        }
        if (ok_set(N, S)) { save_set(N, S); return 1; }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static int eu[MAXE], ev[MAXE];
    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2 || sn <= 0 || sn > MAXN || sm < 0 || sm > MAXE) {
        sn = 0;
        sm = 0;
    }
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) { sn = 0; sm = 0; break; }
    }
    if (d < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    if (sn == 0) {
        sn = 2 * d;
        sm = 0;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) {
                eu[sm] = a;
                ev[sm] = d + b;
                sm++;
            }
    }

    MOORE = moore_bound();
    double t0 = now();
    double tend = t0 + limit * 0.85;
    long bestn = sn;

    if (d >= 3 && D >= 2) {
        if (target_n > bestn) {
            long N = target_n / 2 + 1;
            int comp = 0;
            double until = now() + (tend - now()) * 0.6;
            if (N <= MAXN / 2) {
                if (try_N((int)N, until, &comp)) bestn = 2 * N;
            }
        }
        for (;;) {
            if (now() > tend) break;
            long N = bestn / 2 + 1;
            if (N > MAXN / 2 || 2 * N > MOORE) break;
            int comp = 0;
            if (!try_N((int)N, tend, &comp)) break;
            bestn = 2 * N;
        }
    }

    if (have_haar) {
        int N = HN;
        printf("%d %d\n", 2 * N, N * d);
        for (int i = 0; i < N; i++)
            for (int s = 0; s < d; s++)
                printf("%d %d\n", i, N + (i + HS[s]) % N);
    } else {
        printf("%d %d\n", sn, sm);
        for (int e = 0; e < sm; e++) printf("%d %d\n", eu[e], ev[e]);
    }
    return 0;
}
'''

# Best known orders (targets for the record-jump phase in C).
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    target = RECORDS.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, target],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
