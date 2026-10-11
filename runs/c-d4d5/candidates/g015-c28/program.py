"""Bold variant for the weakest target (d=4, D=5). Replaces the lift-and-grow engine with two
new searches over fresh constructions:

1. Bi-Cayley graphs: vertices a_g and b_x for g, x in a finite group G of order N, with a_g ~ b_{gs}
   for s in a connection set S of size d. Left multiplication is an automorphism, so the diameter
   check needs only two BFS runs (from a_e and b_e). Groups are semidirect products Z_m x| Z_k.
   The search anneals S for growing N.
2. Unstructured annealing: a random d-regular bipartite graph on the target order, improved by
   degree-preserving edge swaps against the exact count of pairs at distance > D (bitset BFS).

Every other case falls back to the algebraic starts (K_{d,d}, PG(2,d-1), Araujo-Pardo-Lopez,
W(q)). Every returned graph is checked with lib.is_valid, and the fallback is the best valid
algebraic start.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 160
#define MAXV 512
#define MAXW 8
#define MAXH 256
#define MAXD 8

/* usage: prog d D seed time_limit mode target
 * mode 0: bi-Cayley search over semidirect groups, prints the largest found graph.
 * mode 1: unstructured annealing on a d-regular bipartite graph with `target` vertices.
 * Prints "0 0" when nothing valid is found. */

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
static int gcdi(int a, int b) {
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
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* ---------- semidirect groups Z_m x| Z_k, element a*k+b ---------- */
static int G_m, G_k, G_r;
static int mulT[MAXG][MAXG];
static int invT[MAXG];
static int rp[MAXG];

static void build_group(int m, int k, int r) {
    G_m = m; G_k = k; G_r = r;
    int N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int a = x / k, b = x % k, c = y / k, e = y % k;
            mulT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mulT[x][y] == 0) { invT[x] = y; break; }
}

static void pick_group(int N) {
    static int cm[256], ck[256], cr[256];
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < 256) { cm[cnt] = 1; ck[cnt] = k; cr[cnt] = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcdi(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < 256) { cm[cnt] = m; ck[cnt] = k; cr[cnt] = r; cnt++; }
        }
    }
    int c = rndint(cnt);
    build_group(cm[c], ck[c], cr[c]);
}

/* ---------- bi-Cayley search (mode 0) ---------- */
static int S[MAXD];
static int nb[MAXV][MAXD];
static int dist[MAXV], qu[MAXV];
static int bestN = 0, bestS[MAXD], bestGm, bestGk, bestGr;

static int has_S(int c) {
    for (int i = 0; i < d; i++) if (S[i] == c) return 1;
    return 0;
}

static void build_nb(int N) {
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) nb[g][i] = N + mulT[g][S[i]];
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) nb[N + x][i] = mulT[x][invT[S[i]]];
}

static int bfs_bad(int N, int src) {
    int V = 2 * N, h = 0, t = 0;
    for (int v = 0; v < V; v++) dist[v] = -1;
    dist[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = nb[v][i];
            if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
        }
    }
    return V - t;
}

/* Vertex-transitivity on each side makes two BFS runs (from a_e and b_e) exact. */
static int eval_S(int N) {
    build_nb(N);
    return bfs_bad(N, 0) + bfs_bad(N, N);
}

static void mode_group(void) {
    int hi = (int)(moore_bound() / 2);
    if (hi > MAXG) hi = MAXG;
    while (now() < t_end) {
        int lo = bestN > 0 ? bestN + 1 : hi / 2;
        if (lo < d) lo = d;
        if (lo > hi) break;
        int span = hi - lo < 10 ? hi - lo : 10;
        int N = lo + rndint(span + 1);
        pick_group(N);
        for (int i = 0; i < d; i++) {
            int c, dup;
            do {
                c = rndint(N);
                dup = 0;
                for (int j = 0; j < i; j++) if (S[j] == c) dup = 1;
            } while (dup);
            S[i] = c;
        }
        int cur = eval_S(N);
        double T = 1.5;
        for (int step = 0; step < 3000 && cur > 0; step++) {
            if ((step & 63) == 0 && now() > t_end) break;
            int i = rndint(d);
            int c = rndint(N);
            if (has_S(c)) continue;
            int old = S[i];
            S[i] = c;
            int nw = eval_S(N);
            if (nw <= cur || rnd01() < exp((cur - nw) / T)) cur = nw;
            else S[i] = old;
            T *= 0.999;
            if (T < 0.15) T = 1.5;
        }
        if (cur == 0 && N > bestN) {
            bestN = N;
            bestGm = G_m; bestGk = G_k; bestGr = G_r;
            memcpy(bestS, S, sizeof S);
        }
    }
}

static void output_group(void) {
    int N = bestN;
    build_group(bestGm, bestGk, bestGr);
    memcpy(S, bestS, sizeof S);
    build_nb(N);
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, nb[g][i]);
}

/* ---------- unstructured annealing (mode 1) ---------- */
static int half, nE;
static int ea[MAXH * MAXD], eb[MAXH * MAXD];
static unsigned char Adj[MAXH][MAXH];
static int nbr1[MAXV][MAXD];
static uint64_t cu[MAXV][MAXW], nx[MAXV][MAXW];

static long bad1(int n) {
    int W = (n + 63) / 64;
    int dg[MAXV];
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int e = 0; e < nE; e++) {
        int a = ea[e], b = half + eb[e];
        nbr1[a][dg[a]++] = b;
        nbr1[b][dg[b]++] = a;
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        cu[v][v / 64] |= 1ULL << (v % 64);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cu[v][w];
            for (int i = 0; i < d; i++) {
                int u = nbr1[v][i];
                for (int w = 0; w < W; w++) nx[v][w] |= cu[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) cu[v][w] = nx[v][w];
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(cu[v][w]);
        total += n - c;
    }
    return total / 2;
}

static void init_random1(void) {
    for (;;) {
        memset(Adj, 0, sizeof Adj);
        int ok = 1;
        nE = 0;
        for (int t = 0; t < d && ok; t++) {
            int perm[MAXH];
            for (int i = 0; i < half; i++) perm[i] = i;
            for (int i = half - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < half; i++) {
                if (Adj[i][perm[i]]) { ok = 0; break; }
                Adj[i][perm[i]] = 1;
                ea[nE] = i;
                eb[nE] = perm[i];
                nE++;
            }
        }
        if (ok) return;
    }
}

static void mode_regular(int n) {
    half = n / 2;
    init_random1();
    long cur = bad1(n);
    double T = 1.0;
    long step = 0;
    while (cur > 0 && now() < t_end) {
        if ((++step & 255) == 0 && now() >= t_end) break;
        int e1 = rndint(nE), e2 = rndint(nE);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (Adj[a1][b2] || Adj[a2][b1]) continue;
        Adj[a1][b1] = 0; Adj[a2][b2] = 0;
        Adj[a1][b2] = 1; Adj[a2][b1] = 1;
        eb[e1] = b2; eb[e2] = b1;
        long nw = bad1(n);
        if (nw <= cur || rnd01() < exp((double)(cur - nw) / T)) {
            cur = nw;
        } else {
            Adj[a1][b2] = 0; Adj[a2][b1] = 0;
            Adj[a1][b1] = 1; Adj[a2][b2] = 1;
            eb[e1] = b1; eb[e2] = b2;
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    if (cur == 0) {
        printf("%d %d\n", n, nE);
        for (int e = 0; e < nE; e++) printf("%d %d\n", ea[e], half + eb[e]);
    } else {
        printf("0 0\n");
    }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit mode target\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int mode = atoi(argv[5]);
    int target = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (mode == 0) {
        mode_group();
        if (bestN == 0) printf("0 0\n");
        else output_group();
    } else {
        if (target < 4 || (target % 2) || target > MAXV || target / 2 > MAXH) {
            printf("0 0\n");
            return 0;
        }
        mode_regular(target);
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


def _search_d4d5(best, d, D, seed, budget):
    """Run the bi-Cayley group search, then unstructured annealing above the current best."""
    deadline = time.monotonic() + budget

    b1 = 0.55 * budget
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, b1, 0, 0], timeout=b1 + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass

    while True:
        left = deadline - time.monotonic() - 1.0
        if left < 3 or best[0] % 2:
            break
        before = best[0]
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + 1, left, 1, best[0] + 2],
                             timeout=left + 10)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            break
        if best[0] == before:
            break
    return best


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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    if d == 4 and D == 5:
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 3:
            try:
                best = _search_d4d5(best, d, D, seed, budget)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
