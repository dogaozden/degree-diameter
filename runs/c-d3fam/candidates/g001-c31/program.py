"""Bold D = 3 rebuild: start from the Araujo-Pardo-Lopez record graph (or PG(2,q)),
then run a C hole-walk annealer that grows the graph by two vertices at a time.

Growth step: add a vertex x on one side and y on the other, with spare degree d each.
The annealer moves spare degree around with edge rewires and degree-preserving swaps,
and it minimises the number of vertex pairs at distance greater than D. Every accepted
state with zero cost is saved, and the search grows from it. Any failure falls back to
the largest valid start graph, so the output is always valid.
"""
import time

import lib

TIME_FRAC = 0.8   # fraction of time_limit used for the whole build

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 4096
#define WMAX 64
#define DMAX 64
#define EPOCH 200000LL
#define STALL 150000LL
#define T_HI 1.2
#define T_LO 0.05

static int DEG_, D_;
static int N;
static int col[NCAP], deg[NCAP], nb[NCAP][DMAX];
static int dl[2][NCAP], dn[2], dpos[NCAP];
static uint64_t R0[NCAP * WMAX], R1[NCAP * WMAX];
static uint64_t rs = 88172645463325252ULL;

static int bn = 0, bcol[NCAP], bdeg[NCAP], bnb[NCAP][DMAX];
static int hasbest = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}
static int rint_(int n) {
    return (int)(rnd() % (uint64_t)n);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void defi_update(int v) {
    int c = col[v];
    int want = deg[v] < DEG_;
    if (want && dpos[v] < 0) {
        dpos[v] = dn[c];
        dl[c][dn[c]++] = v;
    } else if (!want && dpos[v] >= 0) {
        int p = dpos[v];
        int last = dl[c][--dn[c]];
        dl[c][p] = last;
        dpos[last] = p;
        dpos[v] = -1;
    }
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (nb[a][k] == b) return 1;
    return 0;
}

static void del_slot(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) { nb[a][k] = nb[a][--deg[a]]; return; }
    }
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
    defi_update(a);
    defi_update(b);
}

static void del_edge(int a, int b) {
    del_slot(a, b);
    del_slot(b, a);
    defi_update(a);
    defi_update(b);
}

/* number of unordered pairs at distance > D_ (unreachable counts as bad) */
static long long bad_pairs(void) {
    int W = (N + 63) >> 6;
    uint64_t *A = R0, *B = R1;
    memset(A, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = B + (size_t)v * W;
            const uint64_t *in = A + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *iu = A + (size_t)nb[v][k] * W;
                for (int w = 0; w < W; w++) out[w] |= iu[w];
            }
        }
        uint64_t *t = A; A = B; B = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(A[(size_t)v * W + w]);
        total += N - cnt;
    }
    return total / 2;
}

static void save_best(void) {
    bn = N;
    for (int v = 0; v < N; v++) {
        bcol[v] = col[v];
        bdeg[v] = deg[v];
        for (int k = 0; k < deg[v]; k++) bnb[v][k] = nb[v][k];
    }
    hasbest = 1;
}

static void restore_best(void) {
    N = bn;
    dn[0] = dn[1] = 0;
    for (int v = 0; v < N; v++) {
        col[v] = bcol[v];
        deg[v] = bdeg[v];
        dpos[v] = -1;
        for (int k = 0; k < deg[v]; k++) nb[v][k] = bnb[v][k];
    }
    for (int v = 0; v < N; v++) defi_update(v);
}

static int grow(void) {
    if (N + 2 > NCAP) return 0;
    int x = N, y = N + 1;
    col[x] = 1;
    col[y] = 0;
    deg[x] = 0;
    deg[y] = 0;
    dpos[x] = -1;
    dpos[y] = -1;
    N += 2;
    defi_update(x);
    defi_update(y);
    return 1;
}

static int pick_vertex(void) {
    for (int t = 0; t < 64; t++) {
        int v = rint_(N);
        if (deg[v] > 0) return v;
    }
    return -1;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return urand() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || d > DMAX || D_ < 1) { printf("0 0\n"); return 0; }
    DEG_ = d;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    clock_t t0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    int *eu, *ev;
    if (n == 0) {
        if (2 * d > NCAP - 2) { printf("0 0\n"); return 0; }
        n = 2 * d;
        m = d * d;
        eu = malloc(sizeof(int) * (size_t)m);
        ev = malloc(sizeof(int) * (size_t)m);
        int idx = 0;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) { eu[idx] = i; ev[idx] = d + j; idx++; }
    } else {
        if (n < 2 || n > NCAP - 2 || m < 0) { printf("0 0\n"); return 0; }
        eu = malloc(sizeof(int) * (size_t)(m + 1));
        ev = malloc(sizeof(int) * (size_t)(m + 1));
        for (int i = 0; i < m; i++) {
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
            if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) {
                printf("0 0\n"); return 0;
            }
        }
    }

    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int a = eu[i], b = ev[i];
        if (deg[a] >= d || deg[b] >= d || has_edge(a, b)) { printf("0 0\n"); return 0; }
        nb[a][deg[a]++] = b;
        nb[b][deg[b]++] = a;
    }

    int *queue = malloc(sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue[tail++] = v; }
                else if (col[v] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    dn[0] = dn[1] = 0;
    for (int v = 0; v < N; v++) dpos[v] = -1;
    for (int v = 0; v < N; v++) defi_update(v);

    long long cur = bad_pairs();
    int alive = 1;
    if (cur == 0) {
        save_best();
        if (grow()) cur = bad_pairs();
        else alive = 0;
    }
    long long epoch_best = cur, last_imp = 0, it = 0;

    while (alive) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tl) break;
        }
        it++;
        double frac = (double)(it % EPOCH) / (double)EPOCH;
        double T = T_HI * pow(T_LO / T_HI, frac);
        int r = rint_(1000);

        if (r < 350) {
            /* degree-preserving double edge swap */
            int v = pick_vertex(), v2 = pick_vertex();
            if (v >= 0 && v2 >= 0) {
                int b = nb[v][rint_(deg[v])];
                int e2 = nb[v2][rint_(deg[v2])];
                int a, bb, c, e;
                if (col[v] == 0) { a = v; bb = b; } else { a = b; bb = v; }
                if (col[v2] == 0) { c = v2; e = e2; } else { c = e2; e = v2; }
                if (a != c && bb != e && !has_edge(a, e) && !has_edge(c, bb)) {
                    del_edge(a, bb);
                    del_edge(c, e);
                    add_edge(a, e);
                    add_edge(c, bb);
                    long long nc = bad_pairs();
                    if (accept(nc - cur, T)) cur = nc;
                    else {
                        del_edge(a, e);
                        del_edge(c, bb);
                        add_edge(a, bb);
                        add_edge(c, e);
                    }
                }
            }
        } else if (r < 420) {
            /* add an edge between two deficient vertices (never increases cost) */
            if (dn[0] > 0 && dn[1] > 0) {
                int a = dl[0][rint_(dn[0])];
                int b = dl[1][rint_(dn[1])];
                if (!has_edge(a, b)) {
                    add_edge(a, b);
                    cur = bad_pairs();
                }
            }
        } else {
            /* rewire one endpoint of an edge onto a deficient vertex of the same side */
            int v = pick_vertex();
            if (v >= 0) {
                int b = nb[v][rint_(deg[v])];
                int p, q;
                if (rnd() & 1) { p = v; q = b; } else { p = b; q = v; }
                int c = col[p];
                if (dn[c] > 0) {
                    int w = dl[c][rint_(dn[c])];
                    if (w != p && !has_edge(w, q)) {
                        del_edge(p, q);
                        add_edge(w, q);
                        long long nc = bad_pairs();
                        if (accept(nc - cur, T)) cur = nc;
                        else {
                            del_edge(w, q);
                            add_edge(p, q);
                        }
                    }
                }
            }
        }

        if (cur < epoch_best) { epoch_best = cur; last_imp = it; }
        if (cur == 0) {
            save_best();
            if (!grow()) break;
            cur = bad_pairs();
            epoch_best = cur;
            last_imp = it;
        } else if (hasbest && it - last_imp > STALL) {
            restore_best();
            if (!grow()) break;
            cur = bad_pairs();
            epoch_best = cur;
            last_imp = it;
        }
    }

    if (!hasbest) { printf("0 0\n"); return 0; }
    long long M = 0;
    for (int v = 0; v < bn; v++) M += bdeg[v];
    M /= 2;
    printf("%d %lld\n", bn, M);
    for (int v = 0; v < bn; v++)
        for (int k = 0; k < bdeg[v]; k++) {
            int u = bnb[v][k];
            if (u > v) printf("%d %d\n", v, u);
        }
    return 0;
}
'''


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _starts(d, D):
    """Valid start graphs for the search, all checked with lib.is_valid."""
    out = [lib.haar_graph(d, range(d))]   # K_{d,d}: always valid for D >= 2
    if D == 3 and d >= 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                g = lib.araujo_lopez_graph(d - 2)
                if lib.is_valid(g[0], g[1], d, D):
                    out.append(g)
            except ValueError:
                pass
        base = _pg_base(d)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            out.append(base)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))   # K_{d,d} is extremal for D = 2

    # Moore-extremal projective plane: nothing to search for.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    starts = _starts(d, D)
    best = max(starts, key=lambda g: g[0])

    if d <= 60:
        elapsed = time.monotonic() - t0
        budget = max(0.3, TIME_FRAC * time_limit - elapsed - 1.5)
        timeout = min(budget + 5.0, time_limit - elapsed - 1.0)
        if timeout > budget:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=best, timeout=timeout)
                n, e = lib.parse_graph_text(out)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
