"""Bold variant: bi-Cayley graphs over generalized dihedral groups Dih(Z_a x Z_b).

Construction:
- Group G = Dih(A), A = Z_a x Z_b, order N = 2ab. Elements (x, y, s), s in {0, 1}, with
  (a1, s1)(a2, s2) = (a1 + sigma(s1) a2, s1 + s2), where sigma(0) = id and sigma(1) = negation.
- Bi-Cayley graph: vertices (0, g) and (1, h), g, h in G. Edge (0, g)-(1, g*s) for s in S, |S| = d.
  This is d-regular and bipartite, with 2|G| = 4ab vertices.
- Left multiplication by G is an automorphism that is transitive on each side. So diameter <= D
  holds iff BFS from (0, e) and from (1, e) reaches everything within D steps. This is a cheap test.
- The C engine climbs over connection sets S (single-element swaps) to minimise unreached pairs.
  It grows the order by ladder steps over m = ab.

Python keeps a validated fallback (K_{d,d}, PG(2,d-1), Araujo-Pardo-Lopez) and returns the
larger of that and the C result only if lib.is_valid accepts it.
"""
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over generalized dihedral groups Dih(Z_a x Z_b).
 * Usage:   prog d D seed time_limit
 * stdout:  "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024            /* group order N = 2ab */
#define MAXV (2 * MAXG)      /* vertices = 2N */
#define MAXD 32
#define STEPS 4000

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int N, M;                 /* N = 2M, M = a*b */
static int mt[MAXG][MAXG];       /* group multiplication table */
static int inv_[MAXG];           /* group inverses */
static int Sg[MAXD], invS[MAXD]; /* connection set and its inverses */
static unsigned char inS[MAXG];

static int bestV = 0, bestE = 0;
static int eu[MAXG * MAXD], ev[MAXG * MAXD];

static int dist[MAXV], qu[MAXV];

/* Element index: s * M + x * b + y, with x in Z_a, y in Z_b, s in {0,1}. */
static void build_group(int a, int b) {
    M = a * b;
    N = 2 * M;
    for (int g = 0; g < N; g++) {
        int s1 = g / M, i1 = g % M, x1 = i1 / b, y1 = i1 % b;
        for (int h = 0; h < N; h++) {
            int s2 = h / M, i2 = h % M, x2 = i2 / b, y2 = i2 % b;
            int x, y;
            if (s1 == 0) {
                x = (x1 + x2) % a;
                y = (y1 + y2) % b;
            } else {
                x = ((x1 - x2) % a + a) % a;
                y = ((y1 - y2) % b + b) % b;
            }
            mt[g][h] = ((s1 + s2) & 1) * M + x * b + y;
        }
    }
    for (int g = 0; g < N; g++)
        for (int h = 0; h < N; h++)
            if (mt[g][h] == 0) { inv_[g] = h; break; }
}

/* Sum over the two side representatives of the number of vertices at distance > D. */
static int bad_count(void) {
    int nv = 2 * N;
    int bad = 0;
    for (int si = 0; si < 2; si++) {
        int src = si == 0 ? 0 : N;
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++];
            if (dist[v] >= D) continue;
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + mt[v][Sg[k]];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int k = 0; k < d; k++) {
                    int u = mt[h][invS[k]];
                    if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[tail++] = u; }
                }
            }
        }
        bad += nv - tail;
    }
    return bad;
}

static void save_best(void) {
    bestV = 2 * N;
    bestE = 0;
    for (int g = 0; g < N; g++)
        for (int k = 0; k < d; k++) {
            eu[bestE] = g;
            ev[bestE] = N + mt[g][Sg[k]];
            bestE++;
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    double moore_half = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        moore_half += pw;
        pw *= (d - 1);
        if (moore_half > 1e8) break;
    }
    double moore = 2.0 * moore_half;

    int cur = 2 * d;  /* K_{d,d} baseline, handled by Python */
    while (now() < t_end) {
        int m = cur / 4 + 1 + rndint(3);
        if (m > MAXG / 2 || 4.0 * m > moore) break;
        if (2 * m <= d) continue;

        int divs[64], nd = 0;
        for (int a = 1; a <= m && nd < 64; a++)
            if (m % a == 0) divs[nd++] = a;
        int a = divs[rndint(nd)];
        int b = m / a;
        build_group(a, b);
        if (N <= d) continue;

        for (int g = 0; g < N; g++) inS[g] = 0;
        for (int k = 0; k < d; k++) {
            int g;
            do g = rndint(N); while (inS[g]);
            inS[g] = 1;
            Sg[k] = g;
            invS[k] = inv_[g];
        }

        int bad = bad_count();
        for (int step = 0; step < STEPS && bad > 0; step++) {
            if ((step & 63) == 0 && now() > t_end) break;
            int k = rndint(d);
            int old = Sg[k], g;
            do g = rndint(N); while (inS[g]);
            inS[old] = 0;
            inS[g] = 1;
            Sg[k] = g;
            invS[k] = inv_[g];
            int nb = bad_count();
            if (nb <= bad || rnd01() < 0.01) {
                bad = nb;
            } else {
                inS[g] = 0;
                inS[old] = 1;
                Sg[k] = old;
                invS[k] = inv_[old];
            }
        }
        if (bad == 0) {
            save_best();
            cur = 2 * N;
        }
    }

    if (bestV > 0) {
        printf("%d %d\n", bestV, bestE);
        for (int i = 0; i < bestE; i++) printf("%d %d\n", eu[i], ev[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


def known_starts(d, D):
    """Algebraic fallback candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    # Safe fallback: K_{d,d} has diameter 2 <= D and degree d.
    best = lib.haar_graph(d, range(d))
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=None, timeout=budget + 4.5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
