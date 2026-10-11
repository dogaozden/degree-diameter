"""Combined diameter-3 search.

Structured starts (each validated with lib.is_valid):
  - projective plane incidence (d-1 prime power) and Araujo-Pardo/Lopez graphs (d-2 prime power),
  - conic blow-up of PG(2,q) (q = d-3 odd),
  - arc-extended PG(2,q): a set SA of points gets new A-vertices and a set SB of lines gets new
    B-vertices, with per-element load limits s = d-q-1,
  - W(q) for D >= 4 with small q, and K_{d,d} as the always-valid fallback.

C engines, run in sequence from the best start:
  1. INSERT engine: inserts a vertex joined to a greedy cover of spare vertices whose radius-(D-1)
     balls cover everything, so the diameter never grows. Perturbs by removing 1-2 vertices and
     restores the best snapshot after large drops.
  2. ADD engine: the same cover-based insertion with bitset balls, on the result of phase 1.

Every result is validated in Python, and the best valid graph seen is returned.
"""
import itertools
import random
import time

import lib

C_INSERT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define INF 100
typedef uint64_t u64;

static int D_, DEG_, CAP, W, n;
static int *deg, *adj, *col, *queue_, *cand, *dv, *sel, *best_sel;
static unsigned char *dist, *used;
static u64 *ball, *unc;
static unsigned long long rs = 88172645463325252ULL;

typedef struct { int n; int *deg; int *adj; int *col; } Snap;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[(size_t)a * DEG_ + deg[a]++] = b;
    adj[(size_t)b * DEG_ + deg[b]++] = a;
}

static void recompute_dist(void) {
    for (int s = 0; s < n; s++) {
        unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++) row[x] = INF;
        row[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (row[v] == INF) {
                    row[v] = (unsigned char)(row[u] + 1);
                    queue_[t++] = v;
                }
            }
        }
    }
}

static int diam_ok(void) {
    for (int s = 0; s < n; s++) {
        const unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] > D_) return 0;
    }
    return 1;
}

static void build_balls(void) {
    for (int v = 0; v < n; v++) {
        u64 *b = ball + (size_t)v * W;
        memset(b, 0, sizeof(u64) * (size_t)W);
        const unsigned char *row = dist + (size_t)v * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] <= D_ - 1) b[x >> 6] |= 1ULL << (x & 63);
    }
}

/* Greedy cover of all current vertices by balls of spare vertices of colour c. */
static int try_insert(int c, int restarts) {
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == c && deg[v] < DEG_) cand[nc++] = v;
    if (nc == 0) return -1;
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < W; w++) unc[w] = 0;
        for (int x = 0; x < n; x++) unc[x >> 6] |= 1ULL << (x & 63);
        int uncount = n, ns = 0;
        memset(used, 0, (size_t)nc);
        while (uncount > 0 && ns < DEG_) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used[i]) continue;
                const u64 *b = ball + (size_t)cand[i] * W;
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(b[w] & unc[w]);
                if (g == 0) continue;
                long long key = (long long)g * 4096 + (long long)(rnd() % 4096);
                if (key > bkey) { bkey = key; bi = i; }
            }
            if (bi < 0) break;
            used[bi] = 1;
            sel[ns++] = cand[bi];
            const u64 *b = ball + (size_t)cand[bi] * W;
            uncount = 0;
            for (int w = 0; w < W; w++) {
                unc[w] &= ~b[w];
                uncount += pc64(unc[w]);
            }
        }
        if (uncount == 0) {
            for (int k = 0; k < ns; k++) best_sel[k] = sel[k];
            return ns;
        }
    }
    return -1;
}

static void insert_vertex(int c, int ns) {
    int v = n++;
    col[v] = 1 - c;
    deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(v, best_sel[k]);
    for (int x = 0; x < v; x++) {
        int m = INF;
        for (int k = 0; k < ns; k++) {
            int t = dist[(size_t)x * CAP + best_sel[k]];
            if (t < m) m = t;
        }
        int dd = m + 1;
        if (dd > INF) dd = INF;
        dv[x] = dd;
    }
    for (int x = 0; x < v; x++) {
        dist[(size_t)x * CAP + v] = (unsigned char)dv[x];
        dist[(size_t)v * CAP + x] = (unsigned char)dv[x];
    }
    dist[(size_t)v * CAP + v] = 0;
    for (int x = 0; x < v; x++) {
        unsigned char *row = dist + (size_t)x * CAP;
        for (int y = 0; y < v; y++) {
            int t = dv[x] + dv[y];
            if (t > INF) t = INF;
            if (t < row[y]) row[y] = (unsigned char)t;
        }
    }
}

static void del_nbr(int u, int x) {
    int *a = adj + (size_t)u * DEG_;
    for (int j = 0; j < deg[u]; j++) {
        if (a[j] == x) {
            a[j] = a[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_vertex(int r) {
    int last = n - 1;
    for (int k = 0; k < deg[r]; k++) del_nbr(adj[(size_t)r * DEG_ + k], r);
    deg[r] = 0;
    if (r != last) {
        for (int k = 0; k < deg[last]; k++) {
            int u = adj[(size_t)last * DEG_ + k];
            int *a = adj + (size_t)u * DEG_;
            for (int j = 0; j < deg[u]; j++) {
                if (a[j] == last) { a[j] = r; break; }
            }
        }
        memcpy(adj + (size_t)r * DEG_, adj + (size_t)last * DEG_, sizeof(int) * (size_t)DEG_);
        deg[r] = deg[last];
        col[r] = col[last];
    }
    deg[last] = 0;
    col[last] = -1;
    n--;
    recompute_dist();
}

static void snap_init(Snap *s) {
    s->n = 0;
    s->deg = calloc((size_t)CAP, sizeof(int));
    s->adj = calloc((size_t)CAP * DEG_, sizeof(int));
    s->col = calloc((size_t)CAP, sizeof(int));
}

static void snap_save(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * DEG_);
}

static void snap_load(Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * DEG_);
    recompute_dist();
}

static void emit_state(int nn, const int *dg, const int *ad) {
    long m = 0;
    for (int v = 0; v < nn; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", nn, m);
    for (int v = 0; v < nn; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = ad[(size_t)v * DEG_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tl = atof(argv[4]);
    DEG_ = d;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0) nin = 0;
    if (min_ < 0) min_ = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 2));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 2));
    int m_read = 0;
    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= nin || b >= nin || a == b) continue;
        eu[m_read] = a;
        ev[m_read] = b;
        m_read++;
    }
    if (nin == 0) {
        nin = 2;
        m_read = 1;
        eu[0] = 0;
        ev[0] = 1;
    }

    CAP = nin + 1500;
    W = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG_, sizeof(int));
    col = malloc(sizeof(int) * (size_t)CAP);
    queue_ = malloc(sizeof(int) * (size_t)CAP);
    cand = malloc(sizeof(int) * (size_t)CAP);
    dv = malloc(sizeof(int) * (size_t)CAP);
    sel = malloc(sizeof(int) * (size_t)DEG_ + sizeof(int));
    best_sel = malloc(sizeof(int) * (size_t)DEG_ + sizeof(int));
    dist = malloc((size_t)CAP * CAP);
    used = malloc((size_t)CAP);
    ball = calloc((size_t)CAP * W, sizeof(u64));
    unc = calloc((size_t)W, sizeof(u64));

    n = nin;
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int i = 0; i < m_read; i++)
        if (deg[eu[i]] < DEG_ && deg[ev[i]] < DEG_) add_edge(eu[i], ev[i]);

    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue_[t++] = v; }
                else if (col[v] == col[u]) bip = 0;
            }
        }
    }
    recompute_dist();
    if (!bip || !diam_ok()) {
        emit_state(n, deg, adj);
        return 0;
    }

    Snap best, tmp;
    snap_init(&best);
    snap_init(&tmp);
    snap_save(&best);
    int best_n = n;

    double t0 = now();
    while (now() - t0 < tl) {
        if (n + 2 >= CAP) break;
        build_balls();
        int inserted = 0;
        int first = rndint(2);
        for (int t = 0; t < 2 && !inserted; t++) {
            int c = (t == 0) ? first : 1 - first;
            int ns = try_insert(c, 6);
            if (ns > 0) {
                insert_vertex(c, ns);
                inserted = 1;
            }
        }
        if (inserted) {
            if (n > best_n) {
                best_n = n;
                snap_save(&best);
            }
            continue;
        }
        snap_save(&tmp);
        int k = 1 + rndint(2);
        for (int j = 0; j < k && n > 2; j++) remove_vertex(rndint(n));
        if (!diam_ok()) snap_load(&tmp);
        if (n < best_n - 3) snap_load(&best);
    }

    emit_state(best.n, best.deg, best.adj);
    return 0;
}
"""

C_ADD = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def _known_start(d, D):
    """Projective plane (d-1 prime power) or Araujo-Pardo/Lopez (d-2 prime power) for D = 3."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Arc-extended PG(2,q) graphs for each prime power q with q + 1 < d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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


def _starts(d, D, deadline, rng):
    out = []
    ks = _known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = _conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    hard_end = t0 + 0.85 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    cands = []
    for g in _starts(d, D, t0 + 0.12 * time_limit, rng):
        try:
            if lib.is_valid(g[0], g[1], d, D):
                cands.append(g)
        except Exception:
            pass
    if lib.is_valid(fallback[0], fallback[1], d, D):
        cands.append(fallback)
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    # Already at the Moore bound: nothing to search.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Phase 1: insertion engine (ruin-and-recreate with bitset covers).
    remaining = hard_end - time.monotonic()
    if remaining > 2.0:
        budget = max(0.5, 0.55 * remaining - 0.5)
        if best[0] < 40:
            budget = min(budget, 3.0)
        try:
            out = lib.run_c(C_INSERT, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 3.0)
            n1, e1 = lib.parse_graph_text(out)
            if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                best = (n1, e1)
        except (RuntimeError, ValueError):
            pass

    # Phase 2: vertex-addition engine from the current best.
    remaining = hard_end - time.monotonic()
    if remaining > 2.0:
        budget = max(0.5, remaining - 1.0)
        try:
            out = lib.run_c(C_ADD, [d, D, seed * 31 + 1, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 3.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
