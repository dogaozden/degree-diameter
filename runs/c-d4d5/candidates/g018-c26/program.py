"""Bi-Cayley group search (replaces the parent's lift search for the weak target).

A bi-Cayley graph over a group G of order N with connection set S (|S| = d, identity in S WLOG)
has vertices A_x, B_x (x in G) and edges A_x ~ B_{xs} for s in S. Left translations act
transitively on A and on B, so the diameter test needs only two BFS runs (from A_e and B_e).
The C engine enumerates semidirect groups Z_m x|_r Z_k of order N, searching N downward:
phase 1 samples connection sets at random across all groups, phase 2 enumerates them exhaustively
for orders above the best sampled hit. The largest valid order found is returned. Python keeps the
algebraic starts (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}) as a safe fallback and validates
every result with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over semidirect groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit [Nlo]   (stdin ignored)
 * stdout: "n m" then m lines "u v" for the largest valid graph found, else K_{d,d}.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXK 32
#define MAXDESC 60000
#define MAXEDGE (MAXG * MAXK)

typedef struct { int N, m, k, r; } Desc;

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

static int gcd(int a, int b) {
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

static int mulT[MAXG * MAXG];
static int invT[MAXG];
static int GN;

static unsigned vis[2 * MAXG];
static unsigned stampv = 0;
static int bq[2 * MAXG];
static int S[MAXK], invS[MAXK], nS;
static int nbr[2 * MAXG][MAXK];
static int dist2[2 * MAXG];

static int edge_u[MAXEDGE], edge_v[MAXEDGE], edge_m;
static int found_N = 0;

static void build_group(int m, int k, int r) {
    static int rp[MAXG];
    GN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            mulT[x * MAXG + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (mulT[x * MAXG + y] == 0) { invT[x] = y; break; }
}

static void set_S(const int *s) {
    nS = d;
    for (int i = 0; i < d; i++) {
        S[i] = s[i];
        invS[i] = invT[s[i]];
    }
}

/* Number of vertices within distance D of src in the bi-Cayley graph.
 * A-vertices are 0..N-1, B-vertices are N..2N-1. */
static int ball(int src) {
    int N = GN;
    if (++stampv == 0) {
        memset(vis, 0, sizeof vis);
        stampv = 1;
    }
    int head = 0, tail = 0;
    vis[src] = stampv;
    bq[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = bq[head];
            if (v < N) {
                const int *row = mulT + v * MAXG;
                for (int i = 0; i < nS; i++) {
                    int u = N + row[S[i]];
                    if (vis[u] != stampv) { vis[u] = stampv; bq[tail++] = u; }
                }
            } else {
                const int *row = mulT + (v - N) * MAXG;
                for (int i = 0; i < nS; i++) {
                    int u = row[invS[i]];
                    if (vis[u] != stampv) { vis[u] = stampv; bq[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static int valid_now(void) {
    return ball(0) == 2 * GN && ball(GN) == 2 * GN;
}

/* Explicit verification of the candidate graph (bipartite, simple, degree d, diameter D). */
static int full_check(void) {
    int N = GN, n = 2 * N;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < nS; i++) nbr[x][i] = N + mulT[x * MAXG + S[i]];
    for (int y = 0; y < N; y++)
        for (int i = 0; i < nS; i++) nbr[N + y][i] = mulT[y * MAXG + invS[i]];
    for (int v = 0; v < n; v++) {
        for (int i = 0; i < nS; i++) {
            int u = nbr[v][i];
            if (u < 0 || u >= n) return 0;
            if ((v < N) == (u < N)) return 0;
            int ok = 0;
            for (int j = 0; j < nS; j++)
                if (nbr[u][j] == v) { ok = 1; break; }
            if (!ok) return 0;
            for (int j = 0; j < i; j++)
                if (nbr[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist2[v] = -1;
        int head = 0, tail = 0;
        dist2[s] = 0;
        bq[tail++] = s;
        while (head < tail) {
            int v = bq[head++];
            if (dist2[v] >= D) continue;
            for (int i = 0; i < nS; i++) {
                int u = nbr[v][i];
                if (dist2[u] < 0) {
                    dist2[u] = dist2[v] + 1;
                    bq[tail++] = u;
                }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

static void record_found(int N) {
    int c = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < nS; i++) {
            edge_u[c] = x;
            edge_v[c] = N + mulT[x * MAXG + S[i]];
            c++;
        }
    edge_m = c;
    found_N = N;
}

/* Returns 1 if a valid set was found (and recorded), 0 if not, -1 on timeout.
 * If C(N-1, d-1) <= sample_limit the sets are enumerated exhaustively (identity in S WLOG,
 * since right translation of S gives an isomorphic graph); otherwise sample_limit random sets. */
static int try_group(int N, double sample_limit) {
    int k = d - 1;
    if (N - 1 < k) return 0;
    double combos = 1.0;
    for (int i = 0; i < k; i++) combos = combos * (N - 1 - i) / (i + 1);
    int s[MAXK];
    long evals = 0;
    if (combos > sample_limit) {
        long cap = (long)sample_limit;
        while (evals < cap) {
            if ((evals & 63) == 0 && now() > t_end) return -1;
            evals++;
            int cnt = 0;
            s[0] = 0;
            while (cnt < k) {
                int v = 1 + rndint(N - 1), dup = 0;
                for (int j = 1; j <= cnt; j++)
                    if (s[j] == v) { dup = 1; break; }
                if (!dup) s[++cnt] = v;
            }
            set_S(s);
            if (valid_now() && full_check()) { record_found(N); return 1; }
        }
        return 0;
    }
    int c[MAXK];
    for (int i = 0; i < k; i++) c[i] = i + 1;
    for (;;) {
        if ((evals++ & 63) == 0 && now() > t_end) return -1;
        s[0] = 0;
        for (int i = 0; i < k; i++) s[i + 1] = c[i];
        set_S(s);
        if (valid_now() && full_check()) { record_found(N); return 1; }
        int i = k - 1;
        while (i >= 0 && c[i] == N - 1 - (k - 1 - i)) i--;
        if (i < 0) break;
        c[i]++;
        for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    }
    return 0;
}

static void print_complete(void) {
    if (d < 1 || d > MAXK) { printf("1 0\n"); return; }
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static Desc desc[MAXDESC];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [Nlo]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int nlo = argc > 5 ? atoi(argv[5]) : 1;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXK || D < 2) { print_complete(); return 0; }

    long Nmax = moore_bound() / 2;
    if (Nmax > MAXG) Nmax = MAXG;
    if (nlo < d) nlo = d;
    if (Nmax < nlo) { print_complete(); return 0; }

    int ndesc = 0;
    for (long N = Nmax; N >= nlo; N--) {
        for (int m = 2; m <= N; m++) {
            if (N % m) continue;
            int k = (int)(N / m);
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                if (ndesc < MAXDESC) {
                    desc[ndesc].N = (int)N;
                    desc[ndesc].m = m;
                    desc[ndesc].k = k;
                    desc[ndesc].r = r;
                    ndesc++;
                }
            }
        }
    }

    /* Phase 1: sample connection sets across all groups, largest orders first. */
    for (int i = 0; i < ndesc; i++) {
        if (now() > t_end) break;
        build_group(desc[i].m, desc[i].k, desc[i].r);
        int res = try_group(desc[i].N, 2000.0);
        if (res != 0) break;
    }

    /* Phase 2: exhaustive search for orders above the best hit so far. */
    for (int i = 0; i < ndesc && now() < t_end; i++) {
        if (desc[i].N <= found_N) break;
        build_group(desc[i].m, desc[i].k, desc[i].r);
        int res = try_group(desc[i].N, 400000.0);
        if (res != 0) break;
    }

    if (found_N > 0) {
        printf("%d %d\n", 2 * found_N, edge_m);
        for (int e = 0; e < edge_m; e++) printf("%d %d\n", edge_u[e], edge_v[e]);
    } else {
        print_complete();
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

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 1.0:
        return best
    nlo = best[0] // 2 + 1  # bi-Cayley graphs have 2N vertices; only larger orders help
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
