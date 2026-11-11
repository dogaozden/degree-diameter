import time

import lib


_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define WMAX ((MAXN + 63) / 64)
#define MAXD 40
#define ITERS 1500

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} State;

static State work, good;
static int d, D;
static uint64_t *rbuf1, *rbuf2;
static int defA[MAXN], defB[MAXN];
static uint64_t rng_s = 0x9E3779B97F4A7C15ULL;
static clock_t cpu_end;
static time_t wall_end;
static int la, lb, lc, le;

static uint64_t rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}
static int rndi(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int time_over(void) {
    return clock() > cpu_end || time(NULL) >= wall_end;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int j = 0; j < work.deg[a]; j++)
        if (work.adj[a][j] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int j = 0; j < work.deg[v]; j++)
        if (work.adj[v][j] == old) { work.adj[v][j] = nw; return; }
}

static void add_edge(int a, int b) {
    work.adj[a][work.deg[a]++] = b;
    work.adj[b][work.deg[b]++] = a;
}

static void del_edge(int a, int b) {
    for (int j = 0; j < work.deg[a]; j++)
        if (work.adj[a][j] == b) {
            work.adj[a][j] = work.adj[a][work.deg[a] - 1];
            work.deg[a]--;
            break;
        }
    for (int j = 0; j < work.deg[b]; j++)
        if (work.adj[b][j] == a) {
            work.adj[b][j] = work.adj[b][work.deg[b] - 1];
            work.deg[b]--;
            break;
        }
}

/* Bad ordered pairs: pairs (v,w) with distance > D (each unordered pair counted twice). */
static long long compute_cost(void) {
    int N = work.n;
    int Wl = (N + 63) >> 6;
    uint64_t *cur = rbuf1, *nxt = rbuf2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * Wl);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * Wl + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = nxt + (size_t)v * Wl;
            const uint64_t *src = cur + (size_t)v * Wl;
            memcpy(out, src, sizeof(uint64_t) * Wl);
            for (int j = 0; j < work.deg[v]; j++) {
                const uint64_t *s2 = cur + (size_t)work.adj[v][j] * Wl;
                for (int w = 0; w < Wl; w++) out[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *row = cur + (size_t)v * Wl;
        int c = 0;
        for (int w = 0; w < Wl; w++) c += popc64(row[w]);
        bad += N - c;
    }
    return bad;
}

static int rand_edge(int *pa, int *pb) {
    if (work.n <= 0) return 0;
    for (int tries = 0; tries < 100000; tries++) {
        int x = rndi(work.n);
        if (work.deg[x] == 0) continue;
        int y = work.adj[x][rndi(work.deg[x])];
        if (work.side[x] == 0) { *pa = x; *pb = y; }
        else { *pa = y; *pb = x; }
        return 1;
    }
    return 0;
}

/* Degree-preserving swap: (a,b),(c,e) -> (a,e),(c,b), a,c on side 0. */
static int try_swap(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b) || !rand_edge(&c, &e)) return 0;
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    repl(a, b, e);
    repl(b, a, c);
    repl(c, e, b);
    repl(e, c, a);
    la = a; lb = b; lc = c; le = e;
    return 1;
}

static void undo_swap(void) {
    int a = la, b = lb, c = lc, e = le;
    repl(a, e, b);
    repl(e, a, c);
    repl(c, b, e);
    repl(b, c, a);
}

/* Greedy: add edges between non-adjacent deficient vertices on opposite sides. */
static int fill_deficits(void) {
    int added = 0;
    for (int pass = 0; pass < 3; pass++) {
        int nA = 0, nB = 0;
        for (int v = 0; v < work.n; v++) {
            if (work.deg[v] < d) {
                if (work.side[v] == 0) defA[nA++] = v;
                else defB[nB++] = v;
            }
        }
        if (!nA || !nB) break;
        int prog = 0;
        for (int i = 0; i < nA; i++) {
            int a = defA[i];
            for (int j = 0; j < nB; j++) {
                int b = defB[j];
                if (work.deg[a] < d && work.deg[b] < d && !has_edge(a, b)) {
                    add_edge(a, b);
                    added++;
                    prog = 1;
                }
            }
        }
        if (!prog) break;
    }
    return added;
}

/* Add one vertex y on a random side; it takes up to d neighbours z on the other side,
   each taken from an edge (x,z) which is removed (x loses a degree, fixed later). */
static int insert_vertex(void) {
    if (work.n >= MAXN - 1) return 0;
    int s = rndi(2);
    int y = work.n++;
    work.side[y] = s;
    work.deg[y] = 0;
    int zs[MAXD];
    int nz = 0;
    int guard = 0;
    while (nz < d && guard < 20000) {
        guard++;
        int z = rndi(work.n - 1);
        if (work.side[z] != 1 - s || work.deg[z] == 0) continue;
        int dup = 0;
        for (int t = 0; t < nz; t++)
            if (zs[t] == z) { dup = 1; break; }
        if (dup) continue;
        zs[nz++] = z;
    }
    if (nz == 0) {
        work.n--;
        return 0;
    }
    for (int t = 0; t < nz; t++) {
        int z = zs[t];
        int x = work.adj[z][rndi(work.deg[z])];
        del_edge(x, z);
        add_edge(y, z);
    }
    return 1;
}

static long long sa_run(int iters, double T0, double T1) {
    long long cur = compute_cost();
    for (int t = 0; t < iters && cur > 0; t++) {
        if (time_over()) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        if (rndu() < 0.03) {
            if (fill_deficits() > 0) cur = compute_cost();
            continue;
        }
        if (!try_swap()) continue;
        long long nc = compute_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) cur = nc;
        else undo_swap();
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rng_s ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rng_s == 0) rng_s = 1;
    for (int i = 0; i < 16; i++) rnd64();
    cpu_end = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    wall_end = time(NULL) + (time_t)budget;

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    work.n = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { printf("0 0\n"); return 0; }
        if (has_edge(u, v)) continue;
        if (work.deg[u] >= d || work.deg[v] >= d) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject odd cycles. */
    {
        int *q = malloc(sizeof(int) * (size_t)n0);
        for (int v = 0; v < n0; v++) work.side[v] = -1;
        for (int s = 0; s < n0; s++) {
            if (work.side[s] != -1) continue;
            work.side[s] = 0;
            int head = 0, tail = 0;
            q[tail++] = s;
            while (head < tail) {
                int u = q[head++];
                for (int j = 0; j < work.deg[u]; j++) {
                    int w = work.adj[u][j];
                    if (work.side[w] == -1) {
                        work.side[w] = 1 - work.side[u];
                        q[tail++] = w;
                    } else if (work.side[w] == work.side[u]) {
                        printf("0 0\n");
                        free(q);
                        return 0;
                    }
                }
            }
        }
        free(q);
    }

    rbuf1 = malloc(sizeof(uint64_t) * (size_t)MAXN * WMAX);
    rbuf2 = malloc(sizeof(uint64_t) * (size_t)MAXN * WMAX);
    if (!rbuf1 || !rbuf2) { printf("0 0\n"); return 0; }

    fill_deficits();
    int have_good = 0;
    if (compute_cost() == 0) {
        good = work;
        have_good = 1;
    } else {
        if (sa_run(20000, 3.0, 0.2) == 0) {
            good = work;
            have_good = 1;
        }
    }

    int batch = 1;
    while (have_good && !time_over() && good.n < MAXN - 2) {
        work = good;
        int k = 0;
        for (int i = 0; i < batch; i++)
            if (insert_vertex()) k++;
        if (k == 0) break;
        fill_deficits();
        long long c = compute_cost();
        if (c > 0) c = sa_run(ITERS, 2.0, 0.2);
        if (c == 0) {
            good = work;
            if (batch < 64) batch *= 2;
        } else {
            if (batch > 1) batch /= 2;
        }
    }

    if (!have_good) {
        printf("0 0\n");
        return 0;
    }
    long long m = 0;
    for (int v = 0; v < good.n; v++) m += good.deg[v];
    m /= 2;
    printf("%d %lld\n", good.n, m);
    for (int v = 0; v < good.n; v++)
        for (int j = 0; j < good.deg[v]; j++)
            if (good.adj[v][j] > v)
                printf("%d %d\n", v, good.adj[v][j]);
    return 0;
}
"""


def _pg_start(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if q > 60:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    if D >= 3:
        pg = _pg_start(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Growth search in C, starting from the best valid start.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    remaining = budget - (time.monotonic() - t0)
    if remaining >= 2.0 and d <= 40 and best[0] <= 4000:
        cb = remaining - 1.5
        try:
            out = lib.run_c(_C_SOURCE, [d, D, int(seed), round(cb, 2)],
                            stdin_graph=best, timeout=remaining + 4.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
