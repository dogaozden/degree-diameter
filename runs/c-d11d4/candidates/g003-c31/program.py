import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: rarest-first cover growth. A new vertex on colour c is added when
# its neighbourhood (opposite colour, spare degree) covers every existing vertex
# within distance D-1. Greedy cover with random tie-breaking, plus swap local
# search. Adding vertices and edges never breaks diameter <= D.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 6144
#define MAXW (MAXN / 64)
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define ATTEMPTS 40
#define LS_ITERS 150

typedef uint64_t u64;

static int dd, DD, n, W;
static int color[MAXN];
static int deg[MAXN];
static int adj[MAXN][MAXD];
static u64 ball[MAXN][MAXW];
static u64 tmpb[MAXN][MAXW];
static int cntx[MAXN];
static int cand[MAXN];
static int ncand;
static char taken[MAXN];
static int chosen[MAXD];
static int nch;
static u64 rs = 88172645463325252ULL;
static double deadline_s;
static int eu[MAXE], ev[MAXE];
static int n_in, m_in;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int k) {
    return (int)(rnd64() % (u64)k);
}

static double now_s(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int count_bits(const u64 *a) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(a[w]);
    return c;
}

static int count_union(const u64 *a, const u64 *b) {
    int c = 0;
    for (int w = 0; w < W; w++) c += pc64(a[w] | b[w]);
    return c;
}

static void compute_balls(int r) {
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(ball[v], 0, sizeof(u64) * W);
        ball[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            u64 *t = tmpb[v];
            memcpy(t, ball[v], sizeof(u64) * W);
            for (int k = 0; k < deg[v]; k++) {
                const u64 *bu = ball[adj[v][k]];
                for (int w = 0; w < W; w++) t[w] |= bu[w];
            }
        }
        for (int v = 0; v < n; v++) memcpy(ball[v], tmpb[v], sizeof(u64) * W);
    }
}

static int bipartite_color(void) {
    static int queue[MAXN];
    for (int v = 0; v < n; v++) color[v] = -1;
    for (int s = 0; s < n; s++) {
        if (color[s] != -1) continue;
        color[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (color[v] == -1) {
                    color[v] = 1 - color[u];
                    queue[qt++] = v;
                } else if (color[v] == color[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static int greedy_cover(void) {
    u64 cov[MAXW];
    for (int x = 0; x < n; x++) cntx[x] = 0;
    for (int i = 0; i < ncand; i++) {
        const u64 *b = ball[cand[i]];
        for (int w = 0; w < W; w++) {
            u64 bits = b[w];
            while (bits) {
                cntx[(w << 6) + __builtin_ctzll(bits)]++;
                bits &= bits - 1;
            }
        }
    }
    memset(cov, 0, sizeof(u64) * W);
    nch = 0;
    int covered = 0;
    while (covered < n && nch < dd) {
        int bx = -1, bc = 0x7fffffff, ties = 0;
        for (int x = 0; x < n; x++) {
            if ((cov[x >> 6] >> (x & 63)) & 1ULL) continue;
            if (cntx[x] <= 0) return 0;
            if (cntx[x] < bc) {
                bc = cntx[x];
                bx = x;
                ties = 1;
            } else if (cntx[x] == bc) {
                ties++;
                if (rnd_int(ties) == 0) bx = x;
            }
        }
        int noisy = (rnd_int(100) < 15);
        int bs = -1;
        long long bsc = -1;
        for (int i = 0; i < ncand; i++) {
            int s = cand[i];
            if (taken[s]) continue;
            if (!((ball[s][bx >> 6] >> (bx & 63)) & 1ULL)) continue;
            long long sc;
            if (noisy) {
                sc = rnd_int(1 << 30);
            } else {
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(ball[s][w] & ~cov[w]);
                sc = (long long)g * 4096 + rnd_int(4096);
            }
            if (sc > bsc) {
                bsc = sc;
                bs = s;
            }
        }
        if (bs < 0) return 0;
        taken[bs] = 1;
        chosen[nch++] = bs;
        for (int w = 0; w < W; w++) {
            u64 bits = ball[bs][w];
            covered += pc64(bits & ~cov[w]);
            cov[w] |= bits;
            while (bits) {
                cntx[(w << 6) + __builtin_ctzll(bits)]--;
                bits &= bits - 1;
            }
        }
    }
    return covered == n;
}

static int cover_ls(void) {
    u64 cc[MAXW], rest[MAXW];
    for (int it = 0; it <= LS_ITERS; it++) {
        memset(cc, 0, sizeof(u64) * W);
        for (int j = 0; j < nch; j++)
            for (int w = 0; w < W; w++) cc[w] |= ball[chosen[j]][w];
        int cur = n - count_bits(cc);
        if (cur == 0) return 1;
        if (it == LS_ITERS) break;
        int i = rnd_int(nch);
        memset(rest, 0, sizeof(u64) * W);
        for (int j = 0; j < nch; j++) {
            if (j == i) continue;
            for (int w = 0; w < W; w++) rest[w] |= ball[chosen[j]][w];
        }
        int bc = -1, bu = 0x7fffffff;
        for (int t = 0; t < 60; t++) {
            int c = cand[rnd_int(ncand)];
            if (taken[c]) continue;
            int u = n - count_union(rest, ball[c]);
            if (u < bu) {
                bu = u;
                bc = c;
            }
        }
        if (bc >= 0 && bu <= cur) {
            taken[chosen[i]] = 0;
            chosen[i] = bc;
            taken[bc] = 1;
        }
    }
    return 0;
}

static void add_vertex(int c) {
    int v = n++;
    color[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        adj[s][deg[s]++] = v;
        adj[v][deg[v]++] = s;
    }
}

static int try_add(void) {
    int first = rnd_int(2);
    for (int t = 0; t < 2; t++) {
        int c = (t == 0) ? first : 1 - first;
        ncand = 0;
        for (int v = 0; v < n; v++)
            if (color[v] == 1 - c && deg[v] < dd) cand[ncand++] = v;
        if (ncand == 0) continue;
        for (int att = 0; att < ATTEMPTS; att++) {
            if (now_s() > deadline_s) return 0;
            for (int i = 0; i < ncand; i++) taken[cand[i]] = 0;
            int ok = greedy_cover();
            if (!ok && nch == dd) ok = cover_ls();
            if (ok) {
                add_vertex(c);
                return 1;
            }
        }
    }
    return 0;
}

static int verify(void) {
    compute_balls(DD);
    for (int v = 0; v < n; v++) {
        if (count_bits(ball[v]) != n) return 0;
        if (deg[v] > dd) return 0;
        for (int k = 0; k < deg[v]; k++)
            if (color[adj[v][k]] == color[v]) return 0;
    }
    return 1;
}

static void print_input(void) {
    printf("%d %d\n", n_in, m_in);
    for (int i = 0; i < m_in; i++) printf("%d %d\n", eu[i], ev[i]);
}

static void print_current(void) {
    long long sum = 0;
    for (int v = 0; v < n; v++) sum += deg[v];
    printf("%d %lld\n", n, sum / 2);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (scanf("%d %d", &n, &m_in) != 2 || n <= 0 || n > MAXN - 2 ||
        m_in < 0 || m_in > MAXE || dd < 1 || dd > MAXD) {
        printf("0 0\n");
        return 0;
    }
    n_in = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || deg[u] >= dd || deg[v] >= dd) {
            printf("0 0\n");
            return 0;
        }
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
        eu[i] = u;
        ev[i] = v;
    }
    if (DD < 2 || !bipartite_color()) {
        print_input();
        return 0;
    }
    deadline_s = now_s() + budget;
    compute_balls(DD - 1);
    while (n < MAXN - 2 && now_s() < deadline_s) {
        if (!try_add()) break;
        compute_balls(DD - 1);
    }
    if (!verify()) {
        print_input();
        return 0;
    }
    print_current();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: simulated-annealing repair. Moves: degree-preserving edge switches,
# edge additions between deficient opposite-side vertices, and vertex insertion
# that steals edges from saturated vertices. Cost = number of pairs at distance
# > D. The largest valid snapshot is printed.
# ----------------------------------------------------------------------------

C_SA = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 4096
#define MAXD 64
#define WMAX 64
#define STALL 6000
#define TEMP 0.35

static int n, d, D;
static int deg[MAXN];
static int adjv[MAXN][MAXD];
static int col[MAXN];
static int sn;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];
static int have_valid;
static int ie_u[MAXN * MAXD / 2 + 8], ie_v[MAXN * MAXD / 2 + 8];
static int m_in;
static uint64_t BUF[2][MAXN][WMAX];
static uint64_t rs;
static int mv_a, mv_b, mv_a2, mv_b2;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adjv[a][k] == b) return 1;
    return 0;
}
static void rm_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adjv[a][k] == b) {
            adjv[a][k] = adjv[a][--deg[a]];
            return;
        }
    }
}
static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}
static void rm_edge(int a, int b) {
    rm_half(a, b);
    rm_half(b, a);
}

static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t (*A)[WMAX] = BUF[0];
    uint64_t (*B)[WMAX] = BUF[1];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) A[v][w] = 0;
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) B[v][w] = A[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjv[v][k];
                for (int w = 0; w < W; w++) B[v][w] |= A[u][w];
            }
        }
        uint64_t (*t)[WMAX] = A;
        A = B;
        B = t;
    }
    long cnt = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(A[v][w]);
        cnt += n - pc;
    }
    return cnt / 2;
}

static int propose_switch(void) {
    for (int t = 0; t < 50; t++) {
        int a = rndi(n), b, a2, b2;
        if (deg[a] == 0) continue;
        b = adjv[a][rndi(deg[a])];
        if (col[a] == 1) { int tmp = a; a = b; b = tmp; }
        a2 = rndi(n);
        if (deg[a2] == 0) continue;
        b2 = adjv[a2][rndi(deg[a2])];
        if (col[a2] == 1) { int tmp = a2; a2 = b2; b2 = tmp; }
        if (a == a2 || b == b2) continue;
        if (has_edge(a, b2) || has_edge(a2, b)) continue;
        rm_edge(a, b);
        rm_edge(a2, b2);
        add_edge(a, b2);
        add_edge(a2, b);
        mv_a = a; mv_b = b; mv_a2 = a2; mv_b2 = b2;
        return 1;
    }
    return 0;
}

static int propose_add(void) {
    static int x0[MAXN], y1[MAXN];
    int nx = 0, ny = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) x0[nx++] = v;
            else y1[ny++] = v;
        }
    }
    if (nx == 0 || ny == 0) return 0;
    for (int t = 0; t < 30; t++) {
        int x = x0[rndi(nx)], y = y1[rndi(ny)];
        if (!has_edge(x, y)) {
            add_edge(x, y);
            mv_a = x; mv_b = y;
            return 1;
        }
    }
    return 0;
}

static void undo_move(int kind) {
    if (kind == 0) {
        rm_edge(mv_a, mv_b2);
        rm_edge(mv_a2, mv_b);
        add_edge(mv_a, mv_b);
        add_edge(mv_a2, mv_b2);
    } else {
        rm_edge(mv_a, mv_b);
    }
}

static void shuffle_ints(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void insert_vertex(void) {
    static int defi[MAXN], other[MAXN];
    int nc = rndi(2), oc = 1 - nc;
    int nf = 0, no = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] != oc) continue;
        if (deg[v] < d) defi[nf++] = v;
        else other[no++] = v;
    }
    shuffle_ints(defi, nf);
    shuffle_ints(other, no);
    int v = n++;
    deg[v] = 0;
    col[v] = nc;
    int taken = 0;
    for (int i = 0; i < nf && taken < d; i++) {
        add_edge(defi[i], v);
        taken++;
    }
    for (int i = 0; i < no && taken < d; i++) {
        int x = other[i];
        int y = adjv[x][rndi(deg[x])];
        rm_edge(x, y);
        add_edge(x, v);
        taken++;
    }
}

static void save_state(void) {
    sn = n;
    memcpy(sdeg, deg, sizeof(int) * (size_t)n);
    memcpy(scol, col, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) memcpy(sadj[v], adjv[v], sizeof(int) * (size_t)deg[v]);
    have_valid = 1;
}

static void restore_state(void) {
    n = sn;
    memcpy(deg, sdeg, sizeof(int) * (size_t)n);
    memcpy(col, scol, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) memcpy(adjv[v], sadj[v], sizeof(int) * (size_t)deg[v]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    double t0 = now_s();

    int nin = 0, min_e = 0;
    if (scanf("%d %d", &nin, &min_e) != 2 || nin < 1 || nin > MAXN - 2 ||
        min_e < 0 || min_e > MAXN * MAXD / 2 || d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = nin;
    int ok = 1;
    for (int i = 0; i < min_e; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
        ie_u[i] = u;
        ie_v[i] = v;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    m_in = min_e;

    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adjv[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long cur = bad_pairs();
    if (cur == 0) save_state();
    long minc = cur;
    long it = 0, last = 0;

    while (now_s() - t0 < budget) {
        it++;
        if (cur == 0) {
            if (!have_valid || n > sn) save_state();
            if (n >= MAXN - 2) break;
            insert_vertex();
            cur = bad_pairs();
            minc = cur;
            last = it;
            continue;
        }
        if (it - last > STALL) {
            if (have_valid) {
                restore_state();
                cur = bad_pairs();
            }
            minc = cur;
            last = it;
            continue;
        }
        int kind, done;
        if (rndi(10) >= 8) {
            kind = 1;
            done = propose_add();
        } else {
            kind = 0;
            done = propose_switch();
        }
        if (!done) continue;
        long nc = bad_pairs();
        long delta = nc - cur;
        int acc = 1;
        if (delta > 0 && !(rndu() < exp(-(double)delta / TEMP))) acc = 0;
        if (acc) {
            cur = nc;
            if (cur < minc) {
                minc = cur;
                last = it;
            }
        } else {
            undo_move(kind);
        }
    }

    if (have_valid) {
        restore_state();
        long m2 = 0;
        for (int v = 0; v < n; v++) m2 += deg[v];
        m2 /= 2;
        printf("%d %ld\n", n, m2);
        for (int u = 0; u < n; u++)
            for (int k = 0; k < deg[u]; k++)
                if (u < adjv[u][k]) printf("%d %d\n", u, adjv[u][k]);
    } else {
        printf("%d %d\n", nin, m_in);
        for (int i = 0; i < m_in; i++) printf("%d %d\n", ie_u[i], ie_v[i]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q + 1, diameter 4, order 2(q+1)(q^2+1)."""
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


def _gq_qs(d, count):
    """Largest prime powers q (q <= 16, q + 1 <= d), up to `count` of them, largest first."""
    return [q for q in range(d - 1, 1, -1) if q <= 16 and lib.is_prime_power(q)][:count]


def _twin_grow(n, edges, d, rng, deadline):
    """A twin of x (same side, same neighbourhood) keeps all distances; needs spare degree on x's neighbours."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _grow_c(n, edges, d, D, budget, seed):
    """Run C cover growth from a valid graph; return (n, edges) if it grew and is valid, else None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_GROW, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 10.0)
        gn, ge = lib.parse_graph_text(out)
    except Exception:
        return None
    if gn > n and lib.is_valid(gn, ge, d, D):
        return gn, ge
    return None


def _sa_c(n, edges, d, D, budget, seed):
    """Run C simulated-annealing repair from a valid graph; return (n, edges) if valid and not smaller."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SA, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 10.0)
        gn, ge = lib.parse_graph_text(out)
    except Exception:
        return None
    if gn >= n and lib.is_valid(gn, ge, d, D):
        return gn, ge
    return None


# ----------------------------------------------------------------------------
# Driver: constructions -> twin growth -> C cover growth (multi-start) ->
# C annealing repair from the best graph found.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end_all = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(gn, ge):
        nonlocal best, best_n
        if gn > best_n and lib.is_valid(gn, ge, d, D):
            best = (gn, ge)
            best_n = gn

    starts = []
    if D == 3:
        for q in [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]:
            starts.append(lib.projective_plane_incidence(q))
    elif D == 4:
        for q in _gq_qs(d, 3):
            g = _gq_w(q)
            starts.append(g)
            tn, te = _twin_grow(g[0], g[1], d, rng, t0 + 0.12 * time_limit)
            starts.append((tn, te))
    for sn, se in starts:
        consider(sn, se)
    if not starts:
        starts.append(best)
    # Use the largest valid start first.
    starts = sorted(starts, key=lambda g: -g[0])

    # Phase A: multi-start C cover growth.
    phase_a_end = t0 + 0.5 * (end_all - t0)
    runs, stale, k = 0, 0, 0
    while time.monotonic() < phase_a_end - 1.0 and stale < 6:
        sn, se = starts[k % len(starts)]
        k += 1
        remaining = phase_a_end - time.monotonic()
        budget = min(remaining - 0.5, max(4.0, 0.15 * time_limit))
        before = best_n
        res = _grow_c(sn, se, d, D, budget, seed * 7919 + runs)
        runs += 1
        if res is not None:
            consider(res[0], res[1])
        stale = 0 if best_n > before else stale + 1

    # Phase B: C annealing repair from the best graph, using the remaining time.
    if best_n < lib.moore_bound(d, D):
        remaining = end_all - time.monotonic() - 1.5
        if remaining >= 2.0:
            res = _sa_c(best[0], best[1], d, D, remaining, seed + 17)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
