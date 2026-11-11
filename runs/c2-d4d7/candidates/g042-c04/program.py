"""Bi-Cayley search over metacyclic groups for the weakest target (d=4, D=7).

Change from the parent: the C engine no longer searches multi-fibre voltage lifts. It builds
bi-Cayley graphs instead: vertices a_x and b_x for x in a group G of order N, with a_x adjacent to
b_{x s} for each of d connection elements s. The left-regular action of G is an automorphism, so the
diameter is exact after two BFS runs, from a_e and from b_e, and the objective is cheap. The group
family is the semidirect product Z_m x|_r Z_k (cyclic, abelian and dihedral-type groups). Simulated
annealing runs over the connection set S, targeting orders just above the current best. Every
success is re-checked by a full all-pairs BFS, and the Python side re-checks with lib.is_valid. The
best known starting graph is always kept as a fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search over metacyclic groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit < start_graph
 * stdin: "n m" then m edges, or "0 0". stdout: best valid graph ("n m" + edges).
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1200
#define MAXD 32
#define MAXV (2 * MAXG)

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* ---------------------------------------------------------------- group Z_m x|_r Z_k
 * Element a*k+b, product (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static int N;
static int MT[MAXG * MAXG];
static int INV[MAXG];

static void build_group(int m, int k, int r) {
    static int rp[MAXG];
    N = m * k;
    rp[0] = (int)(1 % m);
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int za = (int)(((long)a + (long)rp[b] * c) % m);
            MT[x * N + y] = za * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* Uniform choice among all (m,k,r) with m*k = n, gcd(r,m)=1, r^k = 1 mod m. Returns count. */
static int pick_group(int n, int *pm, int *pk, int *pr) {
    int cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 0; r < m; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint(cnt) == 0) { *pm = m; *pk = k; *pr = r; }
        }
    }
    return cnt;
}

/* ---------------------------------------------------------------- bi-Cayley objective
 * a_x ~ b_{x s} for s in S. Vertex ids: a_x = x, b_y = N + y.
 * Left multiplication is an automorphism, so distances from a_e and b_e determine all of them. */
static int distb[MAXV], qb[MAXV];

static long excess_from(const int *S, int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) distb[v] = -1;
    int head = 0, tail = 0;
    distb[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        int dv = distb[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + MT[v * N + S[i]];
                if (distb[u] < 0) { distb[u] = dv; qb[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = MT[y * N + INV[S[i]]];
                if (distb[u] < 0) { distb[u] = dv; qb[tail++] = u; }
            }
        }
    }
    long tot = 0;
    for (int v = 0; v < V; v++) {
        if (distb[v] < 0) tot += 2;
        else if (distb[v] > D) tot += distb[v] - D;
    }
    return tot;
}

static long excess(const int *S) { return excess_from(S, 0) + excess_from(S, N); }

static int contains(const int *A, int k, int x) {
    for (int i = 0; i < k; i++) if (A[i] == x) return 1;
    return 0;
}

/* Simulated annealing over the d connection elements. Returns 1 and fills outS if excess = 0. */
static int attempt(double until, int *outS) {
    int cur[MAXD], best_s[MAXD];
    for (int i = 0; i < d; i++) {
        int g;
        do g = rndint(N); while (contains(cur, i, g));
        cur[i] = g;
    }
    long cur_v = excess(cur), best_v = cur_v;
    memcpy(best_s, cur, sizeof(int) * d);
    double T0 = 2.0 + 0.02 * (double)cur_v, T = T0;
    int stall = 0;
    for (long s = 0; best_v > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int i = rndint(d), old = cur[i], g;
        do g = rndint(N); while (contains(cur, d, g));
        cur[i] = g;
        long nv = excess(cur);
        long delta = nv - cur_v;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur_v = nv;
        else cur[i] = old;
        if (cur_v < best_v) {
            best_v = cur_v;
            memcpy(best_s, cur, sizeof(int) * d);
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
        if (stall > 4000) {
            memcpy(cur, best_s, sizeof(int) * d);
            int u = rndint(d);
            do g = rndint(N); while (contains(cur, d, g));
            cur[u] = g;
            cur_v = excess(cur);
            T = T0;
            stall = 0;
        }
    }
    memcpy(outS, best_s, sizeof(int) * d);
    return best_v == 0;
}

/* Full verification: every vertex has d distinct neighbours, the graph is connected, and every
 * BFS from every vertex reaches all vertices within D. */
static int nbr[MAXV][MAXD];
static int full_check(const int *S) {
    int V = 2 * N;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            nbr[x][i] = N + MT[x * N + S[i]];
            nbr[N + x][i] = MT[x * N + INV[S[i]]];
        }
    for (int v = 0; v < V; v++)
        for (int i = 0; i < d; i++) {
            if (nbr[v][i] < 0 || nbr[v][i] >= V) return 0;
            for (int j = 0; j < i; j++) if (nbr[v][j] == nbr[v][i]) return 0;
        }
    for (int src = 0; src < V; src++) {
        for (int v = 0; v < V; v++) distb[v] = -1;
        int head = 0, tail = 0;
        distb[src] = 0;
        qb[tail++] = src;
        while (head < tail) {
            int v = qb[head++];
            for (int i = 0; i < d; i++) {
                int u = nbr[v][i];
                if (distb[u] < 0) { distb[u] = distb[v] + 1; qb[tail++] = u; }
            }
        }
        if (tail != V) return 0;
        for (int v = 0; v < V; v++) if (distb[v] > D) return 0;
    }
    return 1;
}

/* ---------------------------------------------------------------- main */
int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Read the whole start graph so it can be echoed back unchanged. */
    size_t cap = 1 << 16, len = 0;
    char *in = malloc(cap);
    if (!in) return 1;
    for (;;) {
        if (cap - len < 4096) {
            cap *= 2;
            in = realloc(in, cap);
            if (!in) return 1;
        }
        size_t got = fread(in + len, 1, cap - len - 1, stdin);
        if (got == 0) break;
        len += got;
    }
    in[len] = 0;

    int start_n = 0, start_m = 0;
    if (sscanf(in, "%d %d", &start_n, &start_m) != 2 || start_n < 0) start_n = 0;

    int best_n = start_n;
    int bM = 0, bK = 0, bR = 0, bS[MAXD];
    int found = 0;
    long moore = moore_bound();

    if (d >= 2 && D >= 2 && d <= MAXD) {
        int Nlow = best_n / 2 + 1;
        if (Nlow < d + 1) Nlow = d + 1;
        const int W = 12;
        while (now() < t_end) {
            if (Nlow >= MAXG || 2L * Nlow > moore) break;
            int Nt = Nlow + rndint(W);
            if (Nt >= MAXG || 2L * Nt > moore) Nt = Nlow;
            int m = 0, k = 0, r = 0;
            if (!pick_group(Nt, &m, &k, &r)) break;
            double rem = t_end - now();
            double slice = rem / 12.0;
            if (slice < 0.5) slice = 0.5;
            if (slice > 4.0) slice = 4.0;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            build_group(m, k, r);
            int S[MAXD];
            if (attempt(until, S) && full_check(S)) {
                if (2 * N > best_n) {
                    best_n = 2 * N;
                    bM = m; bK = k; bR = r;
                    memcpy(bS, S, sizeof(int) * d);
                    found = 1;
                }
                Nlow = N + 1;
            }
        }
    }

    if (found) {
        build_group(bM, bK, bR);
        long m = (long)N * d;
        printf("%d %ld\n", 2 * N, m);
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", x, N + MT[x * N + bS[i]]);
    } else if (start_n > 0) {
        fputs(in, stdout);
    } else {
        int n = 2 * d;
        if (d < 1 || d > MAXD) { printf("0 0\n"); }
        else {
            printf("%d %d\n", n, d * d);
            for (int a = 0; a < d; a++)
                for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        }
    }
    free(in);
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
    """Algebraic candidates (each may be verified by the caller)."""
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    try:
        starts = known_starts(d, D)
    except Exception:
        starts = []
    for n, e in starts:
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
