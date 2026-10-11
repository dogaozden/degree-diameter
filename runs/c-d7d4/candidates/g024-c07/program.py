import itertools
import math
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

#define MAXN 2048
#define MAXW 32
#define MAXDEG 64

typedef uint64_t u64;
typedef u64 Row[MAXW];

static int dmax, Dd;
static int ncap, nalive;
static int nadj[MAXN];
static int adjl[MAXN][MAXDEG];
static int colr[MAXN];
static int alive[MAXN];
static u64 amask[MAXW];
static Row BA[MAXN], BB[MAXN];
static u64 rs;
static double temp_now;
static long cur_cost;

static int snap_ncap = 0, snap_nalive = 0;
static long snap_score = -1;
static int snap_alive[MAXN], snap_col[MAXN], snap_nadj[MAXN];
static int snap_adj[MAXN][MAXDEG];

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int nwords(void) { return (ncap + 63) >> 6; }

static void rebuild_amask(void) {
    memset(amask, 0, sizeof amask);
    nalive = 0;
    for (int v = 0; v < ncap; v++) {
        if (alive[v]) {
            amask[v >> 6] |= 1ULL << (v & 63);
            nalive++;
        }
    }
}

static void set_alive(int v, int val) {
    if (val && !alive[v]) {
        alive[v] = 1;
        amask[v >> 6] |= 1ULL << (v & 63);
        nalive++;
    } else if (!val && alive[v]) {
        alive[v] = 0;
        amask[v >> 6] &= ~(1ULL << (v & 63));
        nalive--;
    }
}

static int has_edge(int a, int b) {
    for (int i = 0; i < nadj[a]; i++)
        if (adjl[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adjl[a][nadj[a]++] = b;
    adjl[b][nadj[b]++] = a;
}

static void del_half(int a, int b) {
    for (int i = 0; i < nadj[a]; i++) {
        if (adjl[a][i] == b) {
            adjl[a][i] = adjl[a][--nadj[a]];
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static void kill_vertex(int v) {
    while (nadj[v] > 0) {
        int u = adjl[v][0];
        del_edge(v, u);
    }
    set_alive(v, 0);
}

/* Bitmask of vertices within distance R of each vertex (dead vertices have no edges). */
static Row *compute_balls(int R) {
    int nw = nwords();
    Row *cur = BA, *nxt = BB;
    for (int v = 0; v < ncap; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < ncap; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < nadj[v]; i++) {
                int u = adjl[v][i];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        Row *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered alive pairs at distance > Dd. */
static long cost_full(void) {
    Row *B = compute_balls(Dd);
    int nw = nwords();
    long bad = 0;
    for (int v = 0; v < ncap; v++) {
        if (!alive[v]) continue;
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(B[v][w] & amask[w]);
        bad += nalive - c;
    }
    return bad / 2;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add cross-side edges between deficient alive vertices. Only shortens distances. */
static void fill_edges(void) {
    int *L = malloc(sizeof(int) * (ncap + 1));
    int *R = malloc(sizeof(int) * (ncap + 1));
    int nl = 0, nr = 0;
    for (int v = 0; v < ncap; v++) {
        if (!alive[v] || nadj[v] >= dmax) continue;
        if (colr[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && nadj[a] < dmax; j++) {
            int b = R[j];
            if (nadj[b] < dmax && !has_edge(a, b)) add_edge(a, b);
        }
    }
    free(L);
    free(R);
}

/* Add one vertex whose neighbourhood covers every alive vertex within Dd-1 of a chosen set. */
static int try_grow(void) {
    int nw = nwords();
    int newc = rndint(2);
    int *cand = malloc(sizeof(int) * (ncap + 1));
    int *gain = malloc(sizeof(int) * (ncap + 1));
    int *used = calloc(ncap + 1, sizeof(int));
    int nc = 0;
    for (int v = 0; v < ncap; v++)
        if (alive[v] && colr[v] == 1 - newc && nadj[v] < dmax) cand[nc++] = v;
    Row *B = compute_balls(Dd - 1);
    Row covered;
    memset(covered, 0, sizeof covered);
    int chosen[MAXDEG];
    int nch = 0, ok = 0;
    for (;;) {
        int cov = 0;
        for (int w = 0; w < nw; w++) cov += pc64(covered[w] & amask[w]);
        if (cov == nalive) {
            ok = 1;
            break;
        }
        if (nch >= dmax) break;
        int bg = 0;
        for (int i = 0; i < nc; i++) {
            gain[i] = 0;
            if (used[i]) continue;
            int s = cand[i], g = 0;
            for (int w = 0; w < nw; w++) g += pc64(B[s][w] & amask[w] & ~covered[w]);
            gain[i] = g;
            if (g > bg) bg = g;
        }
        if (bg == 0) break;
        int thr = bg;
        if (bg > 1 && rnd01() < 0.25) thr = bg - 1;
        int nopt = 0;
        for (int i = 0; i < nc; i++)
            if (!used[i] && gain[i] >= thr && gain[i] > 0) nopt++;
        int pick = rndint(nopt), bi = -1;
        for (int i = 0; i < nc; i++) {
            if (!used[i] && gain[i] >= thr && gain[i] > 0) {
                if (pick == 0) {
                    bi = i;
                    break;
                }
                pick--;
            }
        }
        used[bi] = 1;
        int s = cand[bi];
        chosen[nch++] = s;
        for (int w = 0; w < nw; w++) covered[w] |= B[s][w];
    }
    if (ok) {
        int v = -1;
        for (int x = 0; x < ncap; x++)
            if (!alive[x]) {
                v = x;
                break;
            }
        if (v < 0) {
            if (ncap >= MAXN) ok = 0;
            else v = ncap++;
        }
        if (ok) {
            set_alive(v, 1);
            colr[v] = newc;
            nadj[v] = 0;
            for (int i = 0; i < nch; i++) add_edge(v, chosen[i]);
        }
    }
    free(cand);
    free(gain);
    free(used);
    return ok;
}

/* One simulated-annealing move: bipartite double-edge switch, accepted by bad-pair cost. */
static void sa_step(void) {
    int a = -1, c = -1;
    for (int t = 0; t < 200; t++) {
        int x = rndint(ncap);
        if (alive[x] && colr[x] == 0 && nadj[x] > 0) {
            a = x;
            break;
        }
    }
    for (int t = 0; t < 200; t++) {
        int x = rndint(ncap);
        if (alive[x] && colr[x] == 0 && nadj[x] > 0) {
            c = x;
            break;
        }
    }
    if (a < 0 || c < 0 || a == c) return;
    int b = adjl[a][rndint(nadj[a])];
    int e = adjl[c][rndint(nadj[c])];
    if (b == e) return;
    if (has_edge(a, e) || has_edge(c, b)) return;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    long nc = cost_full();
    long delta = nc - cur_cost;
    if (delta <= 0 || rnd01() < exp(-(double)delta / temp_now)) {
        cur_cost = nc;
        return;
    }
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static void save_snap(void) {
    snap_ncap = ncap;
    snap_nalive = nalive;
    snap_score = nalive;
    memcpy(snap_alive, alive, sizeof(int) * ncap);
    memcpy(snap_col, colr, sizeof(int) * ncap);
    memcpy(snap_nadj, nadj, sizeof(int) * ncap);
    memcpy(snap_adj, adjl, sizeof adjl);
}

static void load_snap(void) {
    ncap = snap_ncap;
    memcpy(alive, snap_alive, sizeof(int) * ncap);
    memcpy(colr, snap_col, sizeof(int) * ncap);
    memcpy(nadj, snap_nadj, sizeof(int) * ncap);
    memcpy(adjl, snap_adj, sizeof adjl);
    rebuild_amask();
}

static void perturb(int k) {
    for (int i = 0; i < k; i++) {
        int v = -1;
        for (int t = 0; t < 1000; t++) {
            int x = rndint(ncap);
            if (alive[x]) {
                v = x;
                break;
            }
        }
        if (v >= 0 && nalive > 8) kill_vertex(v);
    }
}

static void print_snap(void) {
    static int id[MAXN];
    int k = 0;
    for (int v = 0; v < snap_ncap; v++) id[v] = snap_alive[v] ? k++ : -1;
    long m = 0;
    for (int v = 0; v < snap_ncap; v++) {
        if (!snap_alive[v]) continue;
        for (int i = 0; i < snap_nadj[v]; i++)
            if (snap_adj[v][i] > v) m++;
    }
    printf("%d %ld\n", k, m);
    for (int v = 0; v < snap_ncap; v++) {
        if (!snap_alive[v]) continue;
        for (int i = 0; i < snap_nadj[v]; i++) {
            int u = snap_adj[v][i];
            if (u > v) printf("%d %d\n", id[v], id[u]);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dmax = atoi(argv[1]);
    Dd = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (m < 0) m = 0;
    int *eu = malloc(sizeof(int) * (m + 1));
    int *ev = malloc(sizeof(int) * (m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            m = i;
            break;
        }
    }

    int bad = (n < 1 || n > MAXN - 64 || dmax < 1 || dmax >= MAXDEG - 1 || Dd < 2);
    if (!bad) {
        int *dg = calloc(n, sizeof(int));
        for (int i = 0; i < m && !bad; i++) {
            if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n || eu[i] == ev[i]) {
                bad = 1;
            } else {
                dg[eu[i]]++;
                dg[ev[i]]++;
            }
        }
        for (int v = 0; v < n && !bad; v++)
            if (dg[v] > dmax) bad = 1;
        free(dg);
    }
    if (bad) {
        printf("%d %d\n", n, m);
        for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    ncap = n;
    for (int v = 0; v < n; v++) {
        alive[v] = 1;
        nadj[v] = 0;
        colr[v] = -1;
    }
    rebuild_amask();
    for (int i = 0; i < m; i++) add_edge(eu[i], ev[i]);

    /* two-colour the input */
    int *stack = malloc(sizeof(int) * (n + 1));
    for (int s = 0; s < n; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < nadj[u]; i++) {
                int w = adjl[u][i];
                if (colr[w] < 0) {
                    colr[w] = 1 - colr[u];
                    stack[sp++] = w;
                }
            }
        }
    }
    free(stack);

    clock_t t0 = clock();
    double limit = tl * (double)CLOCKS_PER_SEC;

    cur_cost = cost_full();
    save_snap();
    if (cur_cost == 0) {
        snap_score = nalive;
    } else {
        fill_edges();
        cur_cost = cost_full();
        if (cur_cost == 0) save_snap();
        else snap_score = -1;
    }

    unsigned long it = 0;
    long since = 0;
    double frac = 0.0;
    for (;;) {
        if ((it & 15) == 0) {
            clock_t now = clock();
            if ((double)(now - t0) >= limit) break;
            frac = (double)(now - t0) / limit;
        }
        it++;
        temp_now = 0.12 + 0.4 * (1.0 - frac);

        if (cur_cost == 0) {
            if ((long)nalive > snap_score) {
                save_snap();
                since = 0;
            }
            if (try_grow()) {
                cur_cost = cost_full();
                continue;
            }
            if (rnd01() < 0.5) load_snap();
            perturb(1 + rndint(2));
            fill_edges();
            cur_cost = cost_full();
            continue;
        }

        sa_step();
        since++;
        if (since > 40000) {
            load_snap();
            perturb(1 + rndint(3));
            fill_edges();
            cur_cost = cost_full();
            since = 0;
        }
    }

    print_snap();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d, to be thinned into a valid graph."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Thinning a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Voltage lifts over small (cyclic or semidirect) groups.
# A base graph has s vertices per side; each vertex gets exactly d darts.
# ----------------------------------------------------------------------------

def _pick_group(order, rng):
    """Return (order, mul) for a cyclic or a semidirect group of the given order."""
    if order >= 4 and rng.random() < 0.5:
        ks = [k for k in range(2, 13) if order % k == 0 and order // k >= 2]
        rng.shuffle(ks)
        for k in ks:
            m = order // k
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                r = rng.choice(rs)
                try:
                    o, mul, _ = lib.semidirect_group(m, k, r)
                    return o, mul
                except ValueError:
                    continue
    o, mul, _ = lib.cyclic_group(order)
    return o, mul


def _init_darts(s, d, order, rng):
    """Darts (u, v, g): A vertex u, B vertex v (local indices), voltage g."""
    slots = [v for v in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for u in range(s):
        for j in range(d):
            v = slots[u * d + j]
            for _ in range(60):
                g = rng.randrange(order)
                if (u, v, g) not in seen:
                    break
            else:
                return None
            seen.add((u, v, g))
            darts.append((u, v, g))
    return darts


def _lift(s, darts, order, mul):
    """Lift the base graph: A side is 0..s-1, B side is s..2s-1 in the base."""
    return lib.group_lift(2 * s, [(u, s + v, g) for u, v, g in darts], order, mul)


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Hill-climb voltages of random bipartite base lifts until a diameter-D lift appears."""
    base_pick = (1, 1, 2, 2, 3)
    while time.monotonic() < deadline:
        s = rng.choice(base_pick)
        base_n = 2 * s
        lo = best_n // base_n
        order = lo + 1 + rng.randrange(0, max(2, lo // 8 + 1))
        order, mul = _pick_group(order, rng)
        darts = _init_darts(s, d, order, rng)
        if darts is None:
            continue
        n, e = _lift(s, darts, order, mul)
        cost = lib.bad_pairs(n, e, D)
        steps = 0
        while cost > 0 and steps < 250 and time.monotonic() < deadline:
            steps += 1
            i = rng.randrange(len(darts))
            u, v, old = darts[i]
            g2 = rng.randrange(order)
            if g2 == old or (u, v, g2) in set(darts):
                continue
            darts[i] = (u, v, g2)
            n2, e2 = _lift(s, darts, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost or rng.random() < 0.02:
                cost, n, e = c2, n2, e2
            else:
                darts[i] = (u, v, old)
        if cost == 0 and time.monotonic() < deadline:
            if n > best_n and lib.is_valid(n, e, d, D):
                consider(n, e)
                best_n = max(best_n, n)
            n3, e3 = _grow(n, e, d, D, deadline, rng)
            consider(n3, e3)
            best_n = max(best_n, n3)


# ----------------------------------------------------------------------------
# Driver. Fractions of time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, twin trials
#   L  voltage lifts over small groups
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  simulated annealing + kill/repair/regrow in C, from the best graph so far
# Every candidate passes lib.is_valid before it is kept. The fallback is
# haar_graph(d, range(d)), valid for every d >= 1 and D >= 2.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    def at(f):
        return start + f * time_limit

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base, grown; then twin trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups (separate construction family).
    if D >= 2 and d >= 2 and time.monotonic() < at(0.25):
        _lift_search(d, D, best_n, rng, at(0.25), consider)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.32):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.32):
                r = _deletion_trial(d, D, rn, re, rng, at(0.32))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealing engine from the best valid graph found so far.
    if D >= 2 and d >= 2:
        budget = at(0.92) - time.monotonic() - 3.0
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                cn, ce = lib.parse_graph_text(out)
                consider(cn, ce)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
