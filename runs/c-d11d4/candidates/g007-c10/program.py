import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 8192
#define WMAX 128
#define DMAX 64

static int N, DIAM, DEG;
static int adjv[MAXN][DMAX];
static int degv[MAXN];
static int colv[MAXN];
static uint64_t BA[MAXN * WMAX];
static uint64_t BB[MAXN * WMAX];
static int W;
static uint64_t COV[WMAX];
static int CAND[MAXN], USED[MAXN], GAIN[MAXN], L0[MAXN], L1[MAXN], ORD[MAXN], QU[MAXN];
static int CHOSEN[DMAX];
static int SU[MAXN * DMAX], SV[MAXN * DMAX];
static int SM, SN;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int has_edge(int u, int v) {
    for (int i = 0; i < degv[u]; i++)
        if (adjv[u][i] == v) return 1;
    return 0;
}

static void del_arc(int u, int v) {
    for (int i = 0; i < degv[u]; i++) {
        if (adjv[u][i] == v) {
            adjv[u][i] = adjv[u][--degv[u]];
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adjv[u][degv[u]++] = v;
    adjv[v][degv[v]++] = u;
}

static void remove_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Bitmask balls of radius r for all vertices; rows indexed by vertex, W words each. */
static uint64_t *balls(int r) {
    int n = N;
    W = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < degv[v]; i++) {
                const uint64_t *src = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

static int valid_diam(void) {
    uint64_t *b = balls(DIAM);
    int n = N;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = b + (size_t)v * W;
        for (int w = 0; w < W; w++) {
            int rem = n - w * 64;
            uint64_t e = rem >= 64 ? ~0ULL : ((1ULL << rem) - 1);
            if (row[w] != e) return 0;
        }
    }
    return 1;
}

/* Greedy cover of all N vertices by rows of bb for candidates cand[0..nc).
   Returns number chosen (written to out) or 0 on failure. */
static int greedy_cover(const uint64_t *bb, const int *cand, int nc, int randomize, int *out) {
    int n = N;
    memset(COV, 0, sizeof(uint64_t) * W);
    for (int i = 0; i < nc; i++) USED[i] = 0;
    int chosen = 0;
    int covered = 0;
    while (covered < n) {
        if (chosen >= DEG) return 0;
        int best = 0;
        for (int i = 0; i < nc; i++) {
            if (USED[i]) {
                GAIN[i] = -1;
                continue;
            }
            const uint64_t *row = bb + (size_t)cand[i] * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(row[w] & ~COV[w]);
            GAIN[i] = g;
            if (g > best) best = g;
        }
        if (best == 0) return 0;
        int thr = best;
        if (randomize && best > 1 && rndint(4) == 0) thr = best - 1;
        int cnt = 0, pick = -1;
        for (int i = 0; i < nc; i++) {
            if (GAIN[i] >= thr && GAIN[i] > 0) {
                cnt++;
                if (!randomize) {
                    pick = i;
                    break;
                }
                if (rndint(cnt) == 0) pick = i;
            }
        }
        if (pick < 0) return 0;
        USED[pick] = 1;
        out[chosen++] = cand[pick];
        const uint64_t *row = bb + (size_t)cand[pick] * W;
        for (int w = 0; w < W; w++) COV[w] |= row[w];
        covered = 0;
        for (int w = 0; w < W; w++) covered += pc64(COV[w]);
    }
    return chosen;
}

/* Add a vertex of colour nc whose neighbourhood covers all vertices within D-1.
   Keeps it only if the whole graph still has diameter <= D. */
static int try_add(int nc, int attempts) {
    if (N >= MAXN - 2) return 0;
    uint64_t *bb = balls(DIAM - 1);
    int m = 0;
    for (int v = 0; v < N; v++)
        if (colv[v] != nc && degv[v] < DEG) CAND[m++] = v;
    if (m == 0) return 0;
    int k = 0;
    for (int a = 0; a < attempts && k == 0; a++) {
        if (a > 0) shuffle(CAND, m);
        k = greedy_cover(bb, CAND, m, a > 0, CHOSEN);
    }
    if (k == 0) return 0;
    int v = N;
    N++;
    degv[v] = 0;
    colv[v] = nc;
    for (int i = 0; i < k; i++) add_edge(v, CHOSEN[i]);
    if (valid_diam()) return 1;
    for (int i = 0; i < k; i++) remove_edge(v, CHOSEN[i]);
    N--;
    return 0;
}

/* Add edges between deficient opposite-colour vertices (never breaks validity). */
static int saturate(void) {
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (degv[v] < DEG) {
            if (colv[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle(L0, n0);
    shuffle(L1, n1);
    int added = 0;
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && degv[a] < DEG; j++) {
            int b = L1[j];
            if (degv[b] < DEG && !has_edge(a, b)) {
                add_edge(a, b);
                added++;
            }
        }
    }
    return added;
}

/* Twins: a copy of x with the same neighbourhood keeps diameter when D >= 2. */
static int twin_pass(void) {
    int n0 = N, added = 0;
    for (int i = 0; i < n0; i++) ORD[i] = i;
    shuffle(ORD, n0);
    for (int t = 0; t < n0; t++) {
        int x = ORD[t];
        if (N >= MAXN - 2 || degv[x] == 0) continue;
        int ok = 1;
        for (int i = 0; i < degv[x]; i++)
            if (degv[adjv[x][i]] >= DEG) {
                ok = 0;
                break;
            }
        if (!ok) continue;
        int nb[DMAX], dx = degv[x];
        memcpy(nb, adjv[x], sizeof(int) * dx);
        int v = N++;
        degv[v] = 0;
        colv[v] = colv[x];
        for (int i = 0; i < dx; i++) add_edge(v, nb[i]);
        added++;
    }
    return added;
}

static int greedy_grow(double tl) {
    int grew = 0;
    for (;;) {
        int any = 0;
        for (int nc = 0; nc < 2; nc++) {
            if (now() > tl) return grew;
            if (try_add(nc, 6)) {
                any = 1;
                grew = 1;
                saturate();
            }
        }
        if (!any) break;
    }
    return grew;
}

static void grow_all(double tl) {
    for (int r = 0; r < 12 && now() < tl; r++) {
        int a = twin_pass();
        int b = greedy_grow(tl);
        if (!a && !b) break;
    }
}

static void print_current(void) {
    int m = 0;
    for (int v = 0; v < N; v++) m += degv[v];
    printf("%d %d\n", N, m / 2);
    for (int v = 0; v < N; v++)
        for (int i = 0; i < degv[v]; i++)
            if (v < adjv[v][i]) printf("%d %d\n", v, adjv[v][i]);
}

static void print_start(void) {
    printf("%d %d\n", SN, SM);
    for (int i = 0; i < SM; i++) printf("%d %d\n", SU[i], SV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    DEG = d < 1 ? 1 : (d > DMAX ? DMAX : d);
    DIAM = D;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        printf("1 0\n");
        return 0;
    }
    if (n0 < 1 || n0 > MAXN - 2 || m0 < 0 || m0 > MAXN * DMAX) {
        printf("1 0\n");
        return 0;
    }
    SN = n0;
    SM = m0;
    N = n0;
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u = 0, v = 0;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
            SM = i;
            break;
        }
        SU[i] = u;
        SV[i] = v;
        if (!ok) continue;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) ok = 0;
        else if (degv[u] >= DEG || degv[v] >= DEG) ok = 0;
        else if (has_edge(u, v)) ok = 0;
        else add_edge(u, v);
    }
    if (!ok) {
        print_start();
        return 0;
    }

    /* Bipartition check. */
    for (int v = 0; v < N; v++) colv[v] = -1;
    for (int s = 0; s < N && ok; s++) {
        if (colv[s] != -1) continue;
        colv[s] = 0;
        int qh = 0, qt = 0;
        QU[qt++] = s;
        while (qh < qt && ok) {
            int u = QU[qh++];
            for (int i = 0; i < degv[u]; i++) {
                int w = adjv[u][i];
                if (colv[w] == -1) {
                    colv[w] = 1 - colv[u];
                    QU[qt++] = w;
                } else if (colv[w] == colv[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok || DIAM < 2 || !valid_diam()) {
        print_start();
        return 0;
    }

    grow_all(tl);
    while (now() < tl) {
        int a = -1;
        for (int t = 0; t < 200; t++) {
            int c = rndint(N);
            if (degv[c] > 0) {
                a = c;
                break;
            }
        }
        if (a < 0) break;
        int b = adjv[a][rndint(degv[a])];
        remove_edge(a, b);
        int got = 0;
        int c0 = rndint(2);
        for (int t = 0; t < 2 && !got; t++) got = try_add(c0 ^ t, 4);
        if (got) {
            twin_pass();
            saturate();
        } else {
            int done = 0;
            for (int t = 0; t < 2 && !done; t++) {
                int c = rndint(N);
                if (c == a || c == b || colv[c] == colv[a] || degv[c] >= DEG || has_edge(a, c))
                    continue;
                add_edge(a, c);
                if (valid_diam()) {
                    done = 1;
                    saturate();
                } else {
                    remove_edge(a, c);
                }
            }
            if (!done) add_edge(a, b);
        }
    }

    if (!valid_diam()) {
        print_start();
        return 0;
    }
    print_current();
    return 0;
}
"""


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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


def _best_gq(d):
    """W(q) for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best  # K_{d,d} is Moore-optimal for D = 2

    start = None
    if D >= 4:
        start = _best_gq(d)
    if start is None and D >= 3:
        start = _best_pg(d)
    if start is None:
        return best
    consider(start[0], start[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - t0
    budget = 0.80 * time_limit - elapsed
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], stdin_graph=start,
                         timeout=max(2.0, 0.92 * time_limit - elapsed))
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass
    return best
