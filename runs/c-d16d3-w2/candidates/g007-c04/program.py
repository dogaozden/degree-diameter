import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 128
#define MAXE (MAXN * MAXDEG / 2)
#define ATT_ITERS 60000
#define T_HI 2.0
#define T_LO 0.2

static int DEG_MAX = 3;
static int DIAM = 3;
static int n = 0;
static int col[MAXN];
static int deg[MAXN];
static int adjl[MAXN][MAXDEG];
static unsigned char mat[MAXN][MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];
static int baseU[MAXE], baseV[MAXE];
static int baseN = 0, baseM = 0;
static uint64_t rng_state = 88172645463325252ULL;
static double g_deadline = 1.0;

static uint64_t rnd64(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int u, int v) {
    adjl[u][deg[u]++] = v;
    adjl[v][deg[v]++] = u;
    mat[u][v] = 1;
    mat[v][u] = 1;
}

static void del_pos(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adjl[u][k] == v) {
            adjl[u][k] = adjl[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_e(int u, int v) {
    del_pos(u, v);
    del_pos(v, u);
    mat[u][v] = 0;
    mat[v][u] = 0;
}

static void clear_graph(void) {
    memset(deg, 0, sizeof(deg));
    memset(mat, 0, sizeof(mat));
    n = 0;
}

static int load_edges(int nn, int m, const int *eu, const int *ev) {
    if (nn < 1 || nn > MAXN - 2) return 0;
    clear_graph();
    n = nn;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (mat[u][v]) return 0;
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX) return 0;
        add_e(u, v);
    }
    for (int i = 0; i < n; i++) col[i] = -1;
    int stack[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adjl[u][k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stack[sp++] = w;
                }
            }
        }
    }
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (col[adjl[u][k]] == col[u]) return 0;
    return 1;
}

static int load_kdd(int k) {
    int cap = k * k;
    int *u = malloc(sizeof(int) * (size_t)cap);
    int *v = malloc(sizeof(int) * (size_t)cap);
    int c = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++) {
            u[c] = i;
            v[c] = k + j;
            c++;
        }
    int r = load_edges(2 * k, c, u, v);
    free(u);
    free(v);
    return r;
}

static int store_graph(int *su, int *sv) {
    int c = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++) {
            int v = adjl[u][k];
            if (u < v && c < MAXE) {
                su[c] = u;
                sv[c] = v;
                c++;
            }
        }
    return c;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts as bad). Zero means valid. */
static long long cost_fn(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt[v];
            memcpy(dst, cur[v], sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adjl[v][k]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Greedily add random cross-side edges between vertices with spare degree. Never raises the cost. */
static void saturate(void) {
    long long tries = 6LL * n * n;
    for (long long t = 0; t < tries; t++) {
        int a = rndint(n), b = rndint(n);
        if (col[a] == col[b]) continue;
        if (col[a] == 1) {
            int tmp = a;
            a = b;
            b = tmp;
        }
        if (deg[a] >= DEG_MAX || deg[b] >= DEG_MAX || mat[a][b]) continue;
        add_e(a, b);
    }
}

static int pick_vertex(int side, int want_edge) {
    for (int t = 0; t < 128; t++) {
        int v = rndint(n);
        if (col[v] != side) continue;
        if (want_edge) {
            if (deg[v] > 0) return v;
        } else {
            if (deg[v] < DEG_MAX) return v;
        }
    }
    return -1;
}

typedef struct {
    int type;
    int x0, x1, x2, x3;
} Move;

/* type 0: edges (x0,x1),(x2,x3) -> (x0,x3),(x2,x1)   (degree preserving rewire)
   type 1: edge (x0,x1) -> (x2,x1), x2 on the same side as x0   (endpoint shift) */
static int propose(Move *mv) {
    if (rnd01() < 0.6) {
        int a1 = pick_vertex(0, 1);
        int a2 = pick_vertex(0, 1);
        if (a1 < 0 || a2 < 0 || a1 == a2) return 0;
        int b1 = adjl[a1][rndint(deg[a1])];
        int b2 = adjl[a2][rndint(deg[a2])];
        if (b1 == b2 || mat[a1][b2] || mat[a2][b1]) return 0;
        mv->type = 0;
        mv->x0 = a1;
        mv->x1 = b1;
        mv->x2 = a2;
        mv->x3 = b2;
        return 1;
    } else {
        int u = rndint(n);
        if (deg[u] == 0) return 0;
        int v = adjl[u][rndint(deg[u])];
        int u2 = -1;
        for (int t = 0; t < 64; t++) {
            int w = rndint(n);
            if (col[w] == col[u] && w != u && deg[w] < DEG_MAX && !mat[w][v]) {
                u2 = w;
                break;
            }
        }
        if (u2 < 0) return 0;
        mv->type = 1;
        mv->x0 = u;
        mv->x1 = v;
        mv->x2 = u2;
        mv->x3 = -1;
        return 1;
    }
}

static void apply_move(const Move *mv) {
    if (mv->type == 0) {
        del_e(mv->x0, mv->x1);
        del_e(mv->x2, mv->x3);
        add_e(mv->x0, mv->x3);
        add_e(mv->x2, mv->x1);
    } else {
        del_e(mv->x0, mv->x1);
        add_e(mv->x2, mv->x1);
    }
}

static void undo_move(const Move *mv) {
    if (mv->type == 0) {
        del_e(mv->x0, mv->x3);
        del_e(mv->x2, mv->x1);
        add_e(mv->x0, mv->x1);
        add_e(mv->x2, mv->x3);
    } else {
        del_e(mv->x2, mv->x1);
        add_e(mv->x0, mv->x1);
    }
}

/* Metropolis search on the bad-pair count. Edge count and degrees stay fixed under moves. */
static long long anneal(long long cur, int iters, double t_hi, double t_lo) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if (cpu_now() > g_deadline) break;
        double T = t_hi * pow(t_lo / t_hi, (double)it / (double)iters);
        Move mv;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long long c = cost_fn();
        long long delta = c - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c;
        } else {
            undo_move(&mv);
        }
    }
    return cur;
}

static void add_vertices(int mode) {
    /* mode 0: one vertex on each side, 1: one on side 0, 2: one on side 1 */
    if (mode == 0 || mode == 1) {
        col[n] = 0;
        deg[n] = 0;
        n++;
    }
    if (mode == 0 || mode == 2) {
        col[n] = 1;
        deg[n] = 0;
        n++;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || DIAM < 1) {
        printf("1 0\n");
        return 0;
    }
    DEG_MAX = d;
    if (DEG_MAX > MAXDEG) DEG_MAX = MAXDEG;
    rng_state = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    if (rng_state == 0) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd64();
    g_deadline = tl;

    int nn = 0, m = 0;
    if (scanf("%d %d", &nn, &m) != 2) {
        nn = 0;
        m = 0;
    }
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    int got = 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        got++;
    }
    m = got;

    int ok = (nn >= 1) && load_edges(nn, m, eu, ev);
    free(eu);
    free(ev);
    if (!ok) {
        if (DIAM >= 2) {
            ok = load_kdd(DEG_MAX);
        } else {
            int a[1] = {0}, b[1] = {1};
            ok = load_edges(2, 1, a, b);
        }
    }

    saturate();
    long long cur = cost_fn();
    for (int r = 0; r < 10 && cur > 0 && cpu_now() < g_deadline; r++)
        cur = anneal(cur, ATT_ITERS, T_HI, T_LO);
    if (cur > 0) {
        if (DIAM >= 2) {
            load_kdd(DEG_MAX);
        } else {
            int a[1] = {0}, b[1] = {1};
            load_edges(2, 1, a, b);
        }
        cur = cost_fn();
    }
    baseN = n;
    baseM = store_graph(baseU, baseV);

    int fails = 0;
    int attempt = 0;
    while (cpu_now() < g_deadline && n + 2 < MAXN - 1) {
        int mode = attempt % 3;
        add_vertices(mode);
        saturate();
        cur = cost_fn();
        if (cur > 0) cur = anneal(cur, ATT_ITERS, T_HI, T_LO);
        if (cur == 0) {
            baseN = n;
            baseM = store_graph(baseU, baseV);
            fails = 0;
            attempt = 0;
        } else {
            load_edges(baseN, baseM, baseU, baseV);
            attempt++;
            fails++;
            if (fails >= 6) break;
        }
    }

    printf("%d %d\n", baseN, baseM);
    for (int i = 0; i < baseM; i++) printf("%d %d\n", baseU[i], baseV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Start graphs: projective plane PG(2, d-1) when d-1 is a prime power, arc-extended
# PG(2, q) graphs (diameter 3), and K_{d,d} (diameter 2) as the fallback.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _start_candidates(d, D, deadline, rng):
    cands = []
    if D >= 2:
        cands.append(lib.haar_graph(d, range(d)))
    if D < 3:
        return cands
    for q in range(2, d):
        if time.monotonic() > deadline:
            break
        if not lib.is_prime_power(q):
            continue
        m, edges, pl, lp, index, pts = _pg_data(q)
        if q + 1 == d:
            cands.append((2 * m, edges))
            continue
        s = d - q - 1
        if s < 1:
            continue
        best_S = _greedy_arc(m, s, pl, lp, rng, 40, deadline)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(best_S):
                best_S = cs
        if best_S and _loads_ok(best_S, s, m, pl, lp):
            cands.append(_arc_graph(m, edges, pl, best_S, lp))
    return cands


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 7919 + d * 31 + D)
    cand_deadline = t0 + 0.15 * time_limit

    best = None
    for n_c, e_c in _start_candidates(d, D, cand_deadline, rng):
        if n_c > (best[0] if best else 0) and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
    if best is None:
        best = lib.haar_graph(d, range(d))

    remaining = time_limit - (time.monotonic() - t0)
    budget = max(0.5, 0.88 * remaining - 3.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=max(1.0, 0.95 * remaining))
        n2, e2 = lib.parse_graph_text(out)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
