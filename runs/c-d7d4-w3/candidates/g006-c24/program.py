import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define WMAX (NMAX / 64)
#define DMAX 64
#define EMAX (NMAX * DMAX / 2)

typedef uint64_t u64;
typedef u64 Bits[WMAX];

static int N, DEG, DIAM, W;
static int nb[NMAX][DMAX];
static int deg[NMAX];
static int side[NMAX];

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (nb[a][k] == b) return 1;
    return 0;
}
static void del_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) { nb[a][k] = nb[a][--deg[a]]; return; }
    }
}
static void add_edge(int a, int b) { nb[a][deg[a]++] = b; nb[b][deg[b]++] = a; }
static void del_edge(int a, int b) { del_half(a, b); del_half(b, a); }

/* Balls of radius r as bitsets. Output rows 0..N-1 with W words each. */
static Bits BA[NMAX], BB[NMAX], BR[NMAX], BG[NMAX];

static void balls(int r, Bits *out) {
    Bits *cur = BA, *nxt = BB, *tmp;
    W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *src = cur[nb[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) out[v][w] = cur[v][w];
}

/* Number of unordered pairs at distance > DIAM (unreachable included). */
static long cost(void) {
    balls(DIAM, BR);
    long s = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BR[v][w]);
        s += N - c;
    }
    return s / 2;
}

static int bestN = 0, bestM = 0, bestValid = 0;
static int eu[EMAX], ev[EMAX];
static int bestSide[NMAX];

static void snapshot(void) {
    bestN = N;
    bestM = 0;
    for (int a = 0; a < N; a++) {
        bestSide[a] = side[a];
        for (int k = 0; k < deg[a]; k++) {
            int b = nb[a][k];
            if (a < b) { eu[bestM] = a; ev[bestM] = b; bestM++; }
        }
    }
    bestValid = 1;
}

static void restore(void) {
    N = bestN;
    for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = bestSide[v]; }
    for (int i = 0; i < bestM; i++) add_edge(eu[i], ev[i]);
}

typedef struct { int nr, na; int r[2][2]; int a[2][2]; } Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_edge(m->r[i][0], m->r[i][1]);
    for (int i = 0; i < m->na; i++) add_edge(m->a[i][0], m->a[i][1]);
}
static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_edge(m->a[i][0], m->a[i][1]);
    for (int i = 0; i < m->nr; i++) add_edge(m->r[i][0], m->r[i][1]);
}

static int pick_side(int s, int need_spare) {
    for (int t = 0; t < 400; t++) {
        int v = rndint(N);
        if (side[v] != s) continue;
        if (need_spare ? (deg[v] < DEG) : (deg[v] > 0)) return v;
    }
    return -1;
}

/* Degree-preserving double switch, endpoint move to spare capacity, or edge add. */
static int propose(Move *m) {
    m->nr = 0; m->na = 0;
    int kind = rndint(100);
    if (kind < 50) {
        int a = pick_side(0, 0), c = pick_side(0, 0);
        if (a < 0 || c < 0 || a == c) return 0;
        int b = nb[a][rndint(deg[a])];
        int e = nb[c][rndint(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
        m->nr = 2;
        m->r[0][0] = a; m->r[0][1] = b; m->r[1][0] = c; m->r[1][1] = e;
        m->na = 2;
        m->a[0][0] = a; m->a[0][1] = e; m->a[1][0] = c; m->a[1][1] = b;
        return 1;
    } else if (kind < 85) {
        int a = pick_side(0, 0);
        if (a < 0) return 0;
        int b = nb[a][rndint(deg[a])];
        int e = pick_side(1, 1);
        if (e < 0 || e == b || has_edge(a, e)) return 0;
        m->nr = 1; m->r[0][0] = a; m->r[0][1] = b;
        m->na = 1; m->a[0][0] = a; m->a[0][1] = e;
        return 1;
    } else {
        int a = pick_side(0, 1), e = pick_side(1, 1);
        if (a < 0 || e < 0 || has_edge(a, e)) return 0;
        m->na = 1; m->a[0][0] = a; m->a[0][1] = e;
        return 1;
    }
}

/* Add a vertex on a random side, joined to a greedy cover of the other side. */
static int grow(void) {
    if (N >= NMAX - 1) return 0;
    int c = rndint(2);
    balls(DIAM - 1, BG);
    Bits cov;
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[DMAX];
    int nc = 0;
    for (int step = 0; step < DEG; step++) {
        long bestsc = -(1LL << 60);
        int bs = -1;
        for (int s = 0; s < N; s++) {
            if (side[s] == c) continue;
            int used = 0;
            for (int k = 0; k < nc; k++) if (chosen[k] == s) { used = 1; break; }
            if (used) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += pc64(BG[s][w] & ~cov[w]);
            long sc = (long)gain * 1000 + rndint(1000);
            if (deg[s] >= DEG) sc -= 10000000LL;
            if (sc > bestsc) { bestsc = sc; bs = s; }
        }
        if (bs < 0) break;
        chosen[nc++] = bs;
        for (int w = 0; w < W; w++) cov[w] |= BG[bs][w];
    }
    if (nc == 0) return 0;
    int v = N;
    N++;
    deg[v] = 0;
    side[v] = 1 - c;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg[s] >= DEG) {
            int t = nb[s][rndint(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    {
        unsigned long long sd = strtoull(argv[3], NULL, 10);
        rs = 88172645463325252ULL ^ (sd * 2654435761ULL + 12345ULL);
        if (rs == 0) rs = 1;
    }
    double budget = atof(argv[4]);
    if (DEG < 1 || DEG >= DMAX || DIAM < 2) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    int ok = 1;
    if (n0 == 0) {
        N = 2 * DEG;
        for (int i = 0; i < N; i++) side[i] = (i >= DEG);
        for (int i = 0; i < DEG; i++)
            for (int j = 0; j < DEG; j++) add_edge(i, DEG + j);
    } else if (n0 < 0 || n0 > NMAX - 2 || m0 < 0 || m0 > EMAX) {
        ok = 0;
    } else {
        N = n0;
        for (int i = 0; i < m0 && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
            if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
        if (ok) {
            static int stk[NMAX];
            for (int v = 0; v < N; v++) side[v] = -1;
            for (int s = 0; s < N && ok; s++) {
                if (side[s] >= 0) continue;
                side[s] = 0;
                int sp = 0;
                stk[sp++] = s;
                while (sp > 0) {
                    int x = stk[--sp];
                    for (int k = 0; k < deg[x]; k++) {
                        int y = nb[x][k];
                        if (side[y] < 0) { side[y] = 1 - side[x]; stk[sp++] = y; }
                        else if (side[y] == side[x]) { ok = 0; }
                    }
                }
            }
        }
    }
    if (!ok || N < 1) { printf("0 0\n"); return 0; }

    long cur = cost();
    if (cur == 0) snapshot();

    clock_t t0 = clock();
    long it = 0, lastGrow = 0, epochStart = 0;
    const long EPOCH = 4000, STALL = 120000;
    const double THI = 3.0, TLO = 0.2;
    Move mv;
    int alive = 1;
    if (cur == 0) {
        if (!grow()) alive = 0;
        else cur = cost();
    }
    while (alive) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
        }
        it++;
        if (it - epochStart >= EPOCH) epochStart = it;

        /* Stalled: return to the best valid graph and regrow with new randomness. */
        if (bestValid && cur > 0 && it - lastGrow > STALL) {
            restore();
            lastGrow = it;
            if (!grow()) break;
            cur = cost();
            continue;
        }

        if (!propose(&mv)) continue;
        apply_move(&mv);
        long nc = cost();
        double frac = (double)(it - epochStart) / (double)EPOCH;
        double T = THI * pow(TLO / THI, frac);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo_move(&mv);
            continue;
        }
        if (cur == 0) {
            if (!bestValid || N > bestN) snapshot();
            if (!grow()) break;
            cur = cost();
            lastGrow = it;
        }
    }

    if (!bestValid) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", eu[i], ev[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases (projective plane and generalized quadrangle).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for the pre-growth stage.
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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
            for attempt in range(attempts):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Build: structured base, Python pre-growth, then the C annealing engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

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

    if D >= 2:
        base = None
        if D >= 4:
            base = _best_gq(d)
        if base is None and D >= 3:
            base = _best_pg(d)
        if base is not None:
            consider(base[0], base[1])
            n1, e1 = _grow(base[0], list(base[1]), d, D,
                           t0 + 0.08 * time_limit, rng, attempts=16)
            consider(n1, e1)

    # Already at the Moore bound: nothing to search for.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Main stage: C annealing with vertex insertion, double switches and endpoint moves.
    elapsed = time.monotonic() - t0
    wall = 0.90 * time_limit - elapsed
    if wall > 2.0:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, abs(int(seed)) % 1000000007, round(0.8 * wall, 2)],
                stdin_graph=(best_n, best_e),
                timeout=wall,
            )
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
