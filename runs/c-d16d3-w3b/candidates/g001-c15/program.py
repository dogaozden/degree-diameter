"""Bold construction for D = 3: bipartite Haar graphs from difference covering.

For an abelian group G of order N and a set S of d elements, the Haar graph has
parts A = G and B = G, with a_x adjacent to b_{x+s} for each s in S. It is d-regular
and bipartite on 2N vertices. Its diameter is at most 3 exactly when S - S = G, because
a-a and b-b distances are then at most 2 and a-b distances at most 3.

So the search finds S with |S| = d whose differences cover all nonzero elements of G.
That is a simulated-annealing problem with an O(d) move cost, and it can reach orders
above the record. The C engine climbs N one step at a time. Python keeps a valid
projective-plane or K_{d,d} fallback, so every case returns a valid graph.
"""
import time

import lib

C_SOURCE = r'''
/* Difference-covering search for bipartite Haar graphs of diameter 3.
 *
 * Usage:  prog d D seed time_limit        (stdin is ignored)
 * stdout: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 *
 * Group: Z_m1 x Z_m2 with m1*m2 = N (abelian). Vertices 0..N-1 are the A side,
 * N..2N-1 the B side. Edge (x, N + (x + s)) for every s in S.
 * Valid iff every nonzero g in G is a difference s - t of two distinct elements of S.
 * Found by annealing on the number of uncovered differences.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 32
#define MAXG 1000 /* largest group order used: K*(K-1)+1 <= 993 for K <= 32 */

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int K, D;
static double t_end;

/* ------------------------------------------------------------ group tables */

static int N, M1, M2;
static int subt[MAXG][MAXG], addt[MAXG][MAXG];

/* Element x of Z_m1 x Z_m2 is coded as a*m2 + b. */
static void setup_group(int m1, int m2) {
    M1 = m1;
    M2 = m2;
    N = m1 * m2;
    for (int x = 0; x < N; x++) {
        int ax = x / m2, bx = x % m2;
        for (int y = 0; y < N; y++) {
            int ay = y / m2, by = y % m2;
            subt[x][y] = ((ax - ay + m1) % m1) * m2 + ((bx - by + m2) % m2);
            addt[x][y] = ((ax + ay) % m1) * m2 + ((bx + by) % m2);
        }
    }
}

/* ------------------------------------------------------------ search state */

static int S[MAXK];
static unsigned char inS[MAXG];
static int cnt[MAXG]; /* cnt[r] = number of ordered pairs (s, t) in S with s - t = r */
static int uncov;     /* number of r in 1..N-1 with cnt[r] == 0 */

static inline void bump(int r, int dl) {
    if (dl > 0) {
        if (cnt[r] == 0) uncov--;
        cnt[r]++;
    } else {
        cnt[r]--;
        if (cnt[r] == 0) uncov++;
    }
}

/* Remove S[i] from the difference counts (S[i] stays in place). */
static void remove_el(int i) {
    int x = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        bump(subt[x][S[j]], -1);
        bump(subt[S[j]][x], -1);
    }
}

/* Put y at position i and add its differences. */
static void insert_el(int i, int y) {
    S[i] = y;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        bump(subt[y][S[j]], 1);
        bump(subt[S[j]][y], 1);
    }
}

static void rebuild(void) {
    memset(cnt, 0, sizeof cnt);
    memset(inS, 0, sizeof inS);
    uncov = N - 1;
    for (int i = 0; i < K; i++) inS[S[i]] = 1;
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            bump(subt[S[i]][S[j]], 1);
            bump(subt[S[j]][S[i]], 1);
        }
}

/* Simulated annealing from a random S. Returns 1 when S covers all differences. */
static int anneal(long maxit) {
    memset(inS, 0, sizeof inS);
    for (int i = 0; i < K; i++) {
        int y;
        do y = rndint(N); while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    rebuild();
    const double T0 = 1.0, T1 = 0.05;
    const long period = 200000;
    double T = T0;
    for (long it = 0; it < maxit; it++) {
        if (uncov == 0) return 1;
        if ((it & 4095) == 0) {
            if (now() > t_end) return 0;
            T = T0 * pow(T1 / T0, (double)(it % period) / (double)period);
        }
        int i = rndint(K);
        int x = S[i], y;
        do y = rndint(N); while (inS[y]);
        int before = uncov;
        remove_el(i);
        inS[x] = 0;
        insert_el(i, y);
        inS[y] = 1;
        int delta = uncov - before;
        if (delta > 0 && rnd01() >= exp(-delta / T)) {
            remove_el(i);
            inS[y] = 0;
            insert_el(i, x);
            inS[x] = 1;
        }
    }
    return uncov == 0;
}

/* Full BFS check of the current Haar graph (2N vertices, K-regular, diameter <= D). */
static int verify_haar(void) {
    static int adj[2 * MAXG][MAXK];
    static int deg[2 * MAXG], dist[2 * MAXG], queue[2 * MAXG];
    int n = 2 * N;
    memset(deg, 0, sizeof(int) * (size_t)n);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < K; i++) {
            int b = N + addt[x][S[i]];
            if (deg[x] >= K || deg[b] >= K) return 0;
            adj[x][deg[x]++] = b;
            adj[b][deg[b]++] = x;
        }
    for (int v = 0; v < n; v++)
        if (deg[v] != K) return 0;
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < K; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue[tail++] = u;
                }
            }
        }
        if (tail != n) return 0;
        for (int v = 0; v < n; v++)
            if (dist[v] > D) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ main */

static int best_N = 0, best_m1 = 1, best_m2 = 1;
static int best_S[MAXK];

static void print_best(void) {
    if (best_N == 0) {
        printf("0 0\n");
        return;
    }
    setup_group(best_m1, best_m2);
    memcpy(S, best_S, sizeof(int) * (size_t)K);
    printf("%d %ld\n", 2 * N, (long)N * K);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < K; i++)
            printf("%d %d\n", x, N + addt[x][S[i]]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    K = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (D != 3 || K < 2 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    int Nmax = K * (K - 1) + 1; /* S - S has at most K(K-1)+1 elements */

    while (now() < t_end) {
        int Nt = best_N + 1;
        if (Nt < K + 1) Nt = K + 1;   /* need N > K so a free element exists */
        if (Nt > Nmax || Nt > MAXG) break;
        int found = 0;
        while (!found && now() < t_end) {
            int divs[MAXG], nd = 0;
            for (int f = 1; f <= Nt; f++)
                if (Nt % f == 0) divs[nd++] = f;
            int m2 = divs[rndint(nd)];
            setup_group(Nt / m2, m2);
            if (anneal(2000000L) && verify_haar()) {
                found = 1;
                best_N = Nt;
                best_m1 = Nt / m2;
                best_m2 = m2;
                memcpy(best_S, S, sizeof(int) * (size_t)K);
            }
        }
        if (!found) break;
    }
    print_best();
    return 0;
}
'''


def _largest_prime_power_at_most(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _fallbacks(d, D):
    """Valid constructions Python can build directly. Failures are skipped."""
    out = []
    try:
        out.append(lib.haar_graph(d, range(d)))  # K_{d,d}: always valid for D >= 2
    except Exception:
        pass
    if D == 3:
        try:
            q = _largest_prime_power_at_most(d - 1)
            if q is not None:
                out.append(lib.projective_plane_incidence(q))  # degree q+1 <= d
        except Exception:
            pass
        try:
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                out.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = None
    for cand in _fallbacks(d, D):
        try:
            n, edges = cand
            if (best is None or n > best[0]) and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass
    if best is None:
        best = (2 * d, [(i, d + j) for i in range(d) for j in range(d)])

    # Projective planes are Moore graphs: nothing can beat them.
    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if D == 3 and 2 <= d <= 32 and budget > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 8.0)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except Exception:
            pass
    return best
