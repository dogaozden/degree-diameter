"""Bi-Cayley (Haar-type) group search for bipartite degree-diameter graphs.

Instead of voltage lifts with a small base multigraph, this program searches directly for
Haar graphs over finite groups G of order N. Vertices are A_x and B_y for x, y in G, with
A_x ~ B_{x s} for s in S, where S is a set of d distinct group elements. Left multiplication
by G is an automorphism, so only two BFS runs are needed to check diameter D:
  - from A_e (covers all A-A and A-B pairs), and
  - from B_e (covers all B-B pairs).
WLOG S contains the identity (right-multiplying B by t maps S to St). The C engine sweeps
group orders N from the current best upward, samples semidirect groups Z_m x|_r Z_k of order N,
and runs annealing over the remaining d-1 elements of S. A valid S yields a graph on 2N vertices.
The start graph from Python is the fallback, and every returned graph is validated in Python.
"""
import time

import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXD 32
#define MAXGROUPS 8192
#define MAXE 200000

static int d, D;
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

/* Half the Moore bound: the largest possible side size N of a bipartite graph. */
static long moore_half(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 1;
    if (d == 2) return D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return s;
}

/* ---------- groups Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k) ---------- */

typedef struct { int m, k, r; } GDesc;
static GDesc groups[MAXGROUPS];
static int ngroups;
static int N;
static int16_t mul[MAXG][MAXG];
static int invv[MAXG];

static void list_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXGROUPS) { groups[ngroups].m = 1; groups[ngroups].k = k; groups[ngroups].r = 0; ngroups++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGROUPS) { groups[ngroups].m = m; groups[ngroups].k = k; groups[ngroups].r = r; ngroups++; }
        }
    }
}

static void build_group(GDesc G) {
    int m = G.m, k = G.k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mul[x][y] = (int16_t)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mul[x][y] == 0) { invv[x] = y; break; }
}

/* ---------- Haar graph evaluation ---------- */

static int S[MAXD], Sinv[MAXD];
static int dist[2 * MAXG], qu[2 * MAXG];

/* BFS from src up to depth D on the implicit graph. Returns reached count, sets *rb to the
 * number of reached B vertices. Vertices 0..N-1 are A, N..2N-1 are B. */
static int bfs(int src, int *rb) {
    int V = 2 * N, head = 0, tail = 0, nb = 0;
    for (int v = 0; v < V; v++) dist[v] = -1;
    dist[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        int dv = dist[v];
        if (dv >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + mul[v][S[i]];
                if (dist[u] < 0) { dist[u] = dv + 1; qu[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = mul[y][Sinv[i]];
                if (dist[u] < 0) { dist[u] = dv + 1; qu[tail++] = u; }
            }
        }
    }
    for (int i = 0; i < tail; i++)
        if (qu[i] >= N) nb++;
    *rb = nb;
    return tail;
}

/* Number of bad ordered-representative pairs: zero iff the Haar graph has diameter <= D. */
static int eval_bad(void) {
    int rb1, rb2;
    int reach1 = bfs(0, &rb1);
    int bad = 2 * N - reach1;
    bfs(N, &rb2);
    bad += N - rb2;
    return bad;
}

static int in_S(int g, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == g) return 1;
    return 0;
}

static int try_group(GDesc G, long steps) {
    build_group(G);
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int g;
        do { g = 1 + rndint(N - 1); } while (in_S(g, i));
        S[i] = g;
    }
    for (int i = 0; i < d; i++) Sinv[i] = invv[S[i]];
    int cur = eval_bad();
    double T = 1.0;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 511) == 0 && now() > t_end) break;
        int i = 1 + rndint(d - 1);
        int g = rndint(N);
        if (in_S(g, d)) continue;
        int old = S[i];
        S[i] = g;
        Sinv[i] = invv[g];
        int nb = eval_bad();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            S[i] = old;
            Sinv[i] = invv[old];
        }
        T *= 0.9995;
        if (T < 0.1) T = 1.0;
    }
    return cur == 0;
}

/* ---------- start graph and found graph ---------- */

static int st_n = 0, st_m = 0;
static int st_e[MAXE][2];

static void read_start(void) {
    int n, m;
    st_n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || m < 0 || m > MAXE) return;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return;
        if (u < 0 || v < 0 || u >= n || v >= n) return;
        st_e[e][0] = u;
        st_e[e][1] = v;
    }
    st_n = n;
    st_m = m;
}

static int found_n = 0, found_m = 0;
static int found_e[MAXG * MAXD][2];

static void record_found(void) {
    found_m = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) {
            found_e[found_m][0] = x;
            found_e[found_m][1] = N + mul[x][S[i]];
            found_m++;
        }
    found_n = 2 * N;
}

static void print_edges(int n, int m, int (*E)[2]) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", E[i][0], E[i][1]);
}

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
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start();

    long Nmax = moore_half();
    if (Nmax > MAXG) Nmax = MAXG;
    int best_N = st_n / 2;

    if (d >= 2 && d <= MAXD && D >= 1) {
        while (now() < t_end && best_N + 1 <= Nmax) {
            int Nt = best_N + 1;
            if (rndint(3) == 0) Nt += rndint(3);
            if (Nt > Nmax) Nt = best_N + 1;
            if (Nt < d) Nt = d;
            if (Nt > Nmax) break;
            N = Nt;
            list_groups(N);
            GDesc G = groups[rndint(ngroups)];
            if (try_group(G, 4000)) {
                record_found();
                best_N = N;
            }
        }
    }

    if (found_n > st_n && found_n > 0) {
        print_edges(found_n, found_m, found_e);
    } else if (st_n > 0) {
        print_edges(st_n, st_m, st_e);
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

    # Safe fallback: K_{d,d} (valid for D >= 2), then the best algebraic start.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
