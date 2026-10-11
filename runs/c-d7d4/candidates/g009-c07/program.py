import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define DMAX 64
#define ITERS 3000

static int D = 3;
static int S = 3;
static int n = 0;
static int NW = 1;
static int color[MAXN];
static int deg[MAXN];
static int adj[MAXN * DMAX];
static uint64_t BA[MAXN * MAXW];
static uint64_t BB[MAXN * MAXW];
static uint64_t rng_state = 88172645463325252ULL;

typedef struct {
    int n;
    int color[MAXN];
    int deg[MAXN];
    int adj[MAXN * DMAX];
} Snap;

static Snap tmp_s, best_s;

static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void setnw(void) {
    NW = (n + 63) / 64;
    if (NW < 1) NW = 1;
}

static int is_adj(int u, int v) {
    const int *row = adj + (size_t)u * S;
    for (int k = 0; k < deg[u]; k++)
        if (row[k] == v) return 1;
    return 0;
}

static void add_arc(int u, int v) {
    adj[(size_t)u * S + deg[u]] = v;
    deg[u]++;
}

static void del_arc(int u, int v) {
    int *row = adj + (size_t)u * S;
    for (int k = 0; k < deg[u]; k++) {
        if (row[k] == v) {
            row[k] = row[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) { add_arc(u, v); add_arc(v, u); }
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* Bitmask of vertices within distance `rounds` of each vertex. */
static uint64_t *balls(int rounds) {
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * NW);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * NW + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < rounds; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * NW;
            memcpy(dst, cur + (size_t)v * NW, sizeof(uint64_t) * (size_t)NW);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)adj[(size_t)v * S + k] * NW;
                for (int w = 0; w < NW; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > D. */
static long cost(void) {
    uint64_t *b = balls(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = b + (size_t)v * NW;
        for (int w = 0; w < NW; w++) c += popc(row[w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int Lb[MAXN], Rb[MAXN];

/* Add cross-side edges between deficient vertices. Only shortens distances. */
static void fill(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= S) continue;
        if (color[v] == 0) Lb[nl++] = v;
        else Rb[nr++] = v;
    }
    shuffle(Lb, nl);
    shuffle(Rb, nr);
    for (int i = 0; i < nl; i++) {
        int a = Lb[i];
        for (int j = 0; j < nr && deg[a] < S; j++) {
            int b = Rb[j];
            if (deg[b] < S && !is_adj(a, b)) add_edge(a, b);
        }
    }
}

/* Delete vertex x, moving the last vertex into its slot. */
static void remove_vertex(int x) {
    for (int k = deg[x] - 1; k >= 0; k--) {
        int t = adj[(size_t)x * S + k];
        del_arc(t, x);
    }
    deg[x] = 0;
    int L = n - 1;
    if (x != L) {
        for (int k = 0; k < deg[L]; k++) {
            int t = adj[(size_t)L * S + k];
            int *row = adj + (size_t)t * S;
            for (int j = 0; j < deg[t]; j++) {
                if (row[j] == L) {
                    row[j] = x;
                    break;
                }
            }
        }
        memcpy(adj + (size_t)x * S, adj + (size_t)L * S, sizeof(int) * (size_t)S);
        deg[x] = deg[L];
        color[x] = color[L];
    }
    deg[L] = 0;
    n--;
    setnw();
}

/* New vertex on the side opposite `side`, joined to a greedy cover of `side`
   by balls of radius D-1. Full covering vertices lose one random edge. */
static char used[MAXN];

static int add_vertex(int side) {
    if (n >= MAXN - 2) return 0;
    uint64_t *rb = balls(D - 1);
    uint64_t unc[MAXW];
    memset(unc, 0, sizeof(unc));
    for (int v = 0; v < n; v++) unc[v >> 6] |= 1ULL << (v & 63);
    memset(used, 0, sizeof(char) * (size_t)n);
    int chosen[DMAX];
    int nc = 0;
    for (int step = 0; step < S; step++) {
        int best = -1;
        long bestsc = -1;
        for (int s = 0; s < n; s++) {
            if (color[s] != side || used[s]) continue;
            const uint64_t *row = rb + (size_t)s * NW;
            int g = 0;
            for (int w = 0; w < NW; w++) g += popc(row[w] & unc[w]);
            if (g == 0) continue;
            long sc = (long)g * 16 + (long)(rnd64() & 15);
            if (sc > bestsc) {
                bestsc = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        const uint64_t *row = rb + (size_t)best * NW;
        for (int w = 0; w < NW; w++) unc[w] &= ~row[w];
    }
    if (nc == 0) return 0;
    int v = n;
    n++;
    setnw();
    color[v] = 1 - side;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (deg[s] >= S) {
            int t = adj[(size_t)s * S + rndint(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return 1;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static long anneal(int iters) {
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        int a = -1, c = -1;
        for (int t = 0; t < 64 && a < 0; t++) {
            int x = rndint(n);
            if (color[x] == 0 && deg[x] > 0) a = x;
        }
        for (int t = 0; t < 64 && c < 0; t++) {
            int x = rndint(n);
            if (color[x] == 0 && deg[x] > 0 && x != a) c = x;
        }
        if (a < 0 || c < 0) continue;
        int b = adj[(size_t)a * S + rndint(deg[a])];
        int e = adj[(size_t)c * S + rndint(deg[c])];
        if (b == e || is_adj(a, e) || is_adj(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost();
        if (nc <= cur || (nc == cur + 1 && rnd01() < 0.1)) {
            cur = nc;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void take(Snap *s) {
    s->n = n;
    memcpy(s->color, color, sizeof(int) * (size_t)n);
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * S);
}

static void put(const Snap *s) {
    n = s->n;
    setnw();
    memcpy(color, s->color, sizeof(int) * (size_t)n);
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * S);
}

static void print_snap(const Snap *s) {
    long m = 0;
    for (int u = 0; u < s->n; u++)
        for (int k = 0; k < s->deg[u]; k++)
            if (u < s->adj[(size_t)u * S + k]) m++;
    printf("%d %ld\n", s->n, m);
    for (int u = 0; u < s->n; u++)
        for (int k = 0; k < s->deg[u]; k++) {
            int v = s->adj[(size_t)u * S + k];
            if (u < v) printf("%d %d\n", u, v);
        }
}

static void print_input(int gn, int gm, const int *eu, const int *ev) {
    printf("%d %d\n", gn, gm);
    for (int i = 0; i < gm; i++) printf("%d %d\n", eu[i], ev[i]);
}

static int bip_color(int N) {
    static int stack[MAXN];
    for (int v = 0; v < N; v++) color[v] = -1;
    for (int s = 0; s < N; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * S + k];
                if (color[v] == -1) {
                    color[v] = 1 - color[u];
                    stack[sp++] = v;
                } else if (color[v] == color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rng_state = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 1ULL);
    if (rng_state == 0) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int gn = 0, gm = 0;
    if (scanf("%d %d", &gn, &gm) != 2 || gn < 0 || gm < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(gm + 1));
    int *ev = malloc(sizeof(int) * (size_t)(gm + 1));
    for (int i = 0; i < gm; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            gm = i;
            break;
        }
    }

    S = d;
    int feasible = (d >= 1 && d <= DMAX && D >= 2 && gn >= 1 && gn <= MAXN - 2);
    if (feasible) {
        n = gn;
        setnw();
        for (int v = 0; v < n; v++) deg[v] = 0;
        for (int i = 0; i < gm; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || u >= n || v < 0 || v >= n || u == v ||
                deg[u] >= S || deg[v] >= S || is_adj(u, v)) {
                feasible = 0;
                break;
            }
            add_edge(u, v);
        }
    }
    if (feasible) feasible = bip_color(n);
    if (!feasible) {
        print_input(gn, gm, eu, ev);
        return 0;
    }

    clock_t t0 = clock();
    int have_best = 0;
    fill();
    long c = cost();
    for (int i = 0; i < 200 && c > 0 && elapsed(t0) < budget; i++)
        c = anneal(ITERS);
    if (c == 0) {
        take(&best_s);
        have_best = 1;
    }
    if (!have_best) {
        print_input(gn, gm, eu, ev);
        return 0;
    }

    while (elapsed(t0) < budget) {
        int n0 = n;
        take(&tmp_s);
        int k = rndint(10);
        k = k < 6 ? 0 : (k < 9 ? 1 : 2);
        if (k >= n0 - 2) k = 0;
        int ex = (k == 0) ? 1 : rndint(2);
        int good = 1;
        for (int i = 0; i < k; i++) remove_vertex(rndint(n));
        for (int i = 0; i < k + ex; i++) {
            if (!add_vertex(rndint(2))) {
                good = 0;
                break;
            }
            fill();
        }
        long cc = good ? anneal(ITERS) : 1;
        if (cc == 0 && n >= n0) {
            if (n > best_s.n) take(&best_s);
        } else {
            put(&tmp_s);
        }
    }

    print_snap(&best_s);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q <= 8 keeps construction fast)."""
    for q in range(d - 1, 1, -1):
        if q <= 8 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is None:
        base = (best_n, list(best_e))
    consider(base[0], base[1])

    # Native C engine: vertex growth, degree-preserving annealing repair,
    # and plateau moves from the structured base.
    remaining = time_limit - (time.monotonic() - start)
    timeout = remaining - 3.0
    budget = min(0.88 * remaining - 3.0, timeout - 3.0)
    if budget >= 1.0 and D >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=base, timeout=timeout)
            cn, ce = lib.parse_graph_text(out)
            consider(cn, ce)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
