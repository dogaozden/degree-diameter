import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: C-side vertex growth from a projective-plane-based start.
#
# Python builds a start graph (Haar fallback, arc-extended PG(2,q) graphs, or the
# plain PG(2,q) incidence graph), validates it, and hands it to a C engine.
# The C engine grows the graph one vertex at a time. Each new vertex is attached
# greedily to spare-capacity vertices that maximise newly covered vertices within
# distance D. A degree-preserving annealing repairs diameter violations, using
# double-edge switches, edge additions, endpoint rewires and removals. A valid
# snapshot is kept at every step, so the output is always a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 199309L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define REP_ITERS 800
#define GROW_ITERS 1500

typedef uint64_t Row[MAXW];

static int N, DMAX, DIAM, W;
static int deg[MAXN], col[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static Row bufA[MAXN], bufB[MAXN], ballD1[MAXN];
static uint64_t rs;
static double deadline;
static long long cbad;
static int mk, ua, ub, uc, ue;
static int baseN, baseM, have_valid;
static int baseE[MAXE][2];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_e(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    A[u][v] = 1;
    A[v][u] = 1;
}

static void del_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][--deg[u]];
            return;
        }
    }
}

static void rem_e(int u, int v) {
    del_from(u, v);
    del_from(v, u);
    A[u][v] = 0;
    A[v][u] = 0;
}

/* Returns the buffer holding balls of radius r: row v has bit w set iff w is within distance r of v. */
static Row *compute_balls(int r) {
    Row *c = bufA, *x = bufB;
    for (int v = 0; v < N; v++) {
        memset(c[v], 0, sizeof(Row));
        c[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) x[v][w] = c[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) x[v][w] |= c[u][w];
            }
        }
        Row *t = c;
        c = x;
        x = t;
    }
    return c;
}

/* Number of unordered pairs at distance > DIAM (unreachable counts as bad). Zero means valid. */
static long long eval_bad(void) {
    Row *B = compute_balls(DIAM);
    long long s = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(B[v][w]);
        s += N - cnt;
    }
    return s / 2;
}

static int pick(int side) {
    if (N <= 0) return -1;
    for (int t = 0; t < 60; t++) {
        int v = rndint(N);
        if (col[v] == side) return v;
    }
    return -1;
}

static void save_base(void) {
    baseN = N;
    baseM = 0;
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v && baseM < MAXE) {
                baseE[baseM][0] = u;
                baseE[baseM][1] = v;
                baseM++;
            }
        }
    }
}

static void restore_base(void) {
    for (int u = 0; u < N; u++) {
        deg[u] = 0;
        for (int v = 0; v < N; v++) A[u][v] = 0;
    }
    N = baseN;
    W = (N + 63) >> 6;
    for (int i = 0; i < baseM; i++) add_e(baseE[i][0], baseE[i][1]);
    cbad = 0;
}

static void print_base(void) {
    printf("%d %d\n", baseN, baseM);
    for (int i = 0; i < baseM; i++) printf("%d %d\n", baseE[i][0], baseE[i][1]);
}

static void undo_move(void) {
    switch (mk) {
    case 0:
        rem_e(ua, ue);
        rem_e(uc, ub);
        add_e(ua, ub);
        add_e(uc, ue);
        break;
    case 1:
        rem_e(ua, ub);
        break;
    case 2:
        rem_e(ua, uc);
        add_e(ua, ub);
        break;
    case 3:
        add_e(ua, ub);
        break;
    default:
        break;
    }
}

/* Degree-preserving and degree-changing annealing on bad-pair count. Returns 1 if valid. */
static int anneal(int iters) {
    for (int it = 0; it < iters; it++) {
        if (cbad == 0) return 1;
        if ((it & 15) == 0 && now() > deadline) return 0;
        double T = 1.0 * (1.0 - (double)it / (double)iters) + 0.03;
        int mv = rndint(100);
        if (mv < 50) {
            int a = pick(0), c = pick(0);
            if (a < 0 || c < 0 || a == c || deg[a] == 0 || deg[c] == 0) continue;
            int b = nb[a][rndint(deg[a])];
            int e = nb[c][rndint(deg[c])];
            if (b == e || A[a][e] || A[c][b]) continue;
            rem_e(a, b);
            rem_e(c, e);
            add_e(a, e);
            add_e(c, b);
            mk = 0; ua = a; ub = b; uc = c; ue = e;
        } else if (mv < 65) {
            int a = pick(0), b = pick(1);
            if (a < 0 || b < 0 || deg[a] >= DMAX || deg[b] >= DMAX || A[a][b]) continue;
            add_e(a, b);
            mk = 1; ua = a; ub = b;
        } else if (mv < 90) {
            int a = pick(0);
            if (a < 0 || deg[a] == 0) continue;
            int b = nb[a][rndint(deg[a])];
            int c = pick(1);
            if (c < 0 || c == b || deg[c] >= DMAX || A[a][c]) continue;
            rem_e(a, b);
            add_e(a, c);
            mk = 2; ua = a; ub = b; uc = c;
        } else {
            int a = pick(0);
            if (a < 0 || deg[a] == 0) continue;
            int b = nb[a][rndint(deg[a])];
            rem_e(a, b);
            mk = 3; ua = a; ub = b;
        }
        long long nbad = eval_bad();
        long long delta = nbad - cbad;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cbad = nbad;
        } else {
            undo_move();
        }
    }
    return cbad == 0;
}

/* Add one vertex greedily attached to spare-capacity vertices of the opposite colour. */
static int grow_vertex(void) {
    if (N >= MAXN - 1 || N < 1) return 0;
    int c = rndint(2);
    int sp = 0;
    for (int v = 0; v < N; v++) if (col[v] == 1 - c && deg[v] < DMAX) sp++;
    if (sp == 0) {
        c = 1 - c;
        for (int v = 0; v < N; v++) if (col[v] == 1 - c && deg[v] < DMAX) sp++;
        if (sp == 0) return 0;
    }
    int x = N;
    N++;
    W = (N + 63) >> 6;
    col[x] = c;
    deg[x] = 0;
    Row *B = compute_balls(DIAM - 1);
    for (int v = 0; v < x; v++) memcpy(ballD1[v], B[v], sizeof(Row));
    Row cov;
    memset(cov, 0, sizeof(Row));
    int chosen = 0;
    while (chosen < DMAX) {
        int best = -1, ties = 0;
        long long bs = -1;
        for (int b = 0; b < x; b++) {
            if (col[b] == c || deg[b] >= DMAX) continue;
            long long s = 0;
            for (int w = 0; w < W; w++) s += pc64(ballD1[b][w] & ~cov[w]);
            if (s > bs) {
                bs = s;
                best = b;
                ties = 1;
            } else if (s == bs) {
                ties++;
                if (rndint(ties) == 0) best = b;
            }
        }
        if (best < 0) break;
        add_e(x, best);
        chosen++;
        for (int w = 0; w < W; w++) cov[w] |= ballD1[best][w];
    }
    if (chosen == 0) {
        N--;
        W = (N + 63) >> 6;
        return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 88172645463325252ULL;
    double budget = atof(argv[4]);
    deadline = now() + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n <= 0 || n > MAXN - 2 || DMAX < 1 || DMAX > MAXD || DIAM < 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) >> 6;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || A[u][v] || deg[u] >= DMAX || deg[v] >= DMAX) {
            ok = 0;
            break;
        }
        add_e(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition by BFS. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    int bip = 1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[qt++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip) {
        save_base();
        print_base();
        return 0;
    }

    cbad = eval_bad();
    have_valid = 0;
    if (cbad == 0) {
        save_base();
        have_valid = 1;
    }

    while (now() < deadline) {
        if (cbad != 0) {
            if (anneal(REP_ITERS)) {
                save_base();
                have_valid = 1;
            } else if (have_valid) {
                restore_base();
            }
            continue;
        }
        save_base();
        have_valid = 1;
        if (!grow_vertex()) {
            /* No spare capacity on the needed side: free slots by removing a random edge. */
            int a = pick(0);
            if (a >= 0 && deg[a] > 0) {
                int b = nb[a][rndint(deg[a])];
                rem_e(a, b);
            }
            cbad = eval_bad();
            continue;
        }
        cbad = eval_bad();
        if (anneal(GROW_ITERS)) {
            save_base();
        } else {
            restore_base();
        }
    }

    if (have_valid) print_base();
    else printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions used for the start graph.
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


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


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by at most caps[t] elements of S."""
    load = [0] * len(caps)
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(len(caps)))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomised greedy capacitated set."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set from greedy, seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences as (point, line) pairs."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus A-vertices and B-vertices."""
    Rset = set(R)
    na, nb_ = len(SA), len(SB)
    n = 2 * m + na + nb_
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
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
    """Candidate (n, edges) arc-extended projective plane graphs, largest first."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now_t = time.monotonic()
        if now_t > deadline:
            break
        q_deadline = now_t + (deadline - now_t) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs_ = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs_[trial] if trial < len(rs_) else rng.choice(rs_)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


def _largest_pg_start(d):
    """Incidence graph of PG(2, q) for the largest prime power q < d (degree q+1 <= d)."""
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if not qs:
        return None
    return lib.projective_plane_incidence(max(qs))


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3 and d >= 3:
        rng = random.Random(seed * 7919 + d)
        cands = _arc_extensions(d, t0 + 0.2 * time_limit, rng)
        pg = _largest_pg_start(d)
        if pg is not None:
            cands.append(pg)
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c <= best[0]:
                break
            if lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)
                break

    elapsed = time.monotonic() - t0
    budget = 0.92 * time_limit - elapsed - 2.0
    if D >= 2 and d >= 2 and budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 5.0)
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
