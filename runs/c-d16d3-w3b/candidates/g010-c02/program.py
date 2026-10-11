import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over graphs with a penalty for bad pairs.
#
# State: a bipartite graph with max degree d. Energy = -n + W * (number of
# unordered pairs at distance > D). Moves: add a vertex with random neighbours
# on the opposite side, delete a random vertex (its neighbours gain capacity),
# or double-edge swaps (keep degrees and bipartiteness). The best state with
# zero bad pairs is kept and printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} State;

static State S, B, BEST;
static int d_, D_;
static uint64_t rs_;
static int seen_[MAXN];
static int stamp_ = 0;
static int qbuf_[MAXN];
static int stk_[MAXN];

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double urand(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void copy_state(State *dst, const State *src) {
    dst->n = src->n;
    for (int i = 0; i < src->n; i++) {
        dst->deg[i] = src->deg[i];
        dst->col[i] = src->col[i];
        memcpy(dst->adj[i], src->adj[i], sizeof(int) * src->deg[i]);
    }
}

static int has_edge(const State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++)
        if (s->adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(State *s, int a, int b) {
    s->adj[a][s->deg[a]++] = b;
    s->adj[b][s->deg[b]++] = a;
}

static void del_arc(State *s, int a, int b) {
    for (int k = 0; k < s->deg[a]; k++) {
        if (s->adj[a][k] == b) {
            s->adj[a][k] = s->adj[a][s->deg[a] - 1];
            s->deg[a]--;
            return;
        }
    }
}

static void del_edge(State *s, int a, int b) {
    del_arc(s, a, b);
    del_arc(s, b, a);
}

/* Number of vertices within distance D of src (including src). */
static int reach_count(const State *s, int src, int D) {
    stamp_++;
    int head = 0, tail = 0;
    qbuf_[tail++] = src;
    seen_[src] = stamp_;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int u = qbuf_[head++];
            for (int k = 0; k < s->deg[u]; k++) {
                int v = s->adj[u][k];
                if (seen_[v] != stamp_) {
                    seen_[v] = stamp_;
                    qbuf_[tail++] = v;
                }
            }
        }
    }
    return tail;
}

static long long bad_pairs(const State *s) {
    long long tot = 0;
    for (int v = 0; v < s->n; v++)
        tot += s->n - reach_count(s, v, D_);
    return tot / 2;
}

static int valid_all(const State *s) {
    if (s->n <= 1) return 1;
    for (int v = 0; v < s->n; v++)
        if (reach_count(s, v, D_) != s->n) return 0;
    return 1;
}

/* Proper 2-colouring by BFS; returns 0 if the graph is not bipartite. */
static int color_graph(State *s) {
    for (int i = 0; i < s->n; i++) s->col[i] = -1;
    for (int st = 0; st < s->n; st++) {
        if (s->col[st] != -1) continue;
        s->col[st] = 0;
        int sp = 0;
        stk_[sp++] = st;
        while (sp > 0) {
            int u = stk_[--sp];
            for (int k = 0; k < s->deg[u]; k++) {
                int v = s->adj[u][k];
                if (s->col[v] == -1) {
                    s->col[v] = 1 - s->col[u];
                    stk_[sp++] = v;
                } else if (s->col[v] == s->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void remove_vertex(State *s, int w) {
    for (int k = 0; k < s->deg[w]; k++) {
        int u = s->adj[w][k];
        for (int j = 0; j < s->deg[u]; j++) {
            if (s->adj[u][j] == w) {
                s->adj[u][j] = s->adj[u][--s->deg[u]];
                break;
            }
        }
    }
    int L = s->n - 1;
    if (w != L) {
        for (int k = 0; k < s->deg[L]; k++) {
            int u = s->adj[L][k];
            for (int j = 0; j < s->deg[u]; j++) {
                if (s->adj[u][j] == L) {
                    s->adj[u][j] = w;
                    break;
                }
            }
        }
        s->deg[w] = s->deg[L];
        s->col[w] = s->col[L];
        memcpy(s->adj[w], s->adj[L], sizeof(int) * s->deg[L]);
    }
    s->deg[L] = 0;
    s->n--;
}

/* Add a vertex on a random side, joined to a random set of spare-capacity vertices on the other side. */
static void add_random(State *s) {
    if (s->n >= MAXN - 2) return;
    int c = rndint(2);
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < s->n; u++)
        if (s->col[u] != c && s->deg[u] < d_) cand[nc++] = u;
    if (nc == 0) return;
    int k = d_ - rndint(3);
    if (k < 1) k = 1;
    if (k > nc) k = nc;
    for (int i = 0; i < k; i++) {
        int j = i + rndint(nc - i);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int v = s->n++;
    s->deg[v] = 0;
    s->col[v] = c;
    for (int i = 0; i < k; i++) {
        int u = cand[i];
        s->adj[u][s->deg[u]++] = v;
        s->adj[v][s->deg[v]++] = u;
    }
}

/* Degree-preserving double edge swap: x1-y1, x2-y2  ->  x1-y2, x2-y1 (same colour for x1, x2). */
static void double_swap(State *s) {
    if (s->n < 4) return;
    for (int t = 0; t < 30; t++) {
        int x1 = rndint(s->n);
        if (s->deg[x1] == 0) continue;
        int y1 = s->adj[x1][rndint(s->deg[x1])];
        int x2 = rndint(s->n);
        if (x2 == x1 || s->col[x2] != s->col[x1] || s->deg[x2] == 0) continue;
        int y2 = s->adj[x2][rndint(s->deg[x2])];
        if (y1 == y2) continue;
        if (has_edge(s, x1, y2) || has_edge(s, x2, y1)) continue;
        del_edge(s, x1, y1);
        del_edge(s, x2, y2);
        add_edge(s, x1, y2);
        add_edge(s, x2, y1);
        return;
    }
}

static int build_kdd(State *s, int d) {
    memset(s, 0, sizeof(*s));
    s->n = 2 * d;
    for (int i = 0; i < d; i++) {
        s->col[i] = 0;
        s->col[d + i] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(s, i, d + j);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d_ < 1) d_ = 1;
    if (d_ > MAXD) d_ = MAXD;
    if (budget < 0.1) budget = 0.1;
    rs_ = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rnd64();

    /* Read start graph. */
    static State init;
    memset(&init, 0, sizeof(init));
    int n = 0, m = 0, ok = 1;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n > 0) {
        if (n >= MAXN - 2) ok = 0;
        else init.n = n;
        for (int e = 0; ok && e < m; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            if (init.deg[u] >= d_ || init.deg[v] >= d_ || has_edge(&init, u, v)) { ok = 0; break; }
            add_edge(&init, u, v);
        }
        if (ok && !color_graph(&init)) ok = 0;
        if (ok && !valid_all(&init)) ok = 0;
    } else {
        ok = 0;
    }
    if (!ok) build_kdd(&init, d_);

    copy_state(&S, &init);
    copy_state(&BEST, &init);
    int best_n = BEST.n;

    double t0 = now_s();
    double tend = t0 + budget;
    const double T0 = 0.8, T1 = 0.03, W = 1.0;
    long long bad = bad_pairs(&S);
    double E = -(double)S.n + W * (double)bad;
    long long since = 0;

    for (;;) {
        double t = now_s();
        if (t >= tend) break;
        double frac = (t - t0) / budget;
        if (frac < 0) frac = 0;
        if (frac > 1) frac = 1;
        double T = T0 * pow(T1 / T0, frac);

        copy_state(&B, &S);
        int r = rndint(100);
        if (r < 25) {
            add_random(&S);
        } else if (r < 35) {
            if (S.n > 3) remove_vertex(&S, rndint(S.n));
        } else if (r < 70) {
            double_swap(&S);
        } else {
            double_swap(&S);
            double_swap(&S);
        }

        long long nb = bad_pairs(&S);
        double nE = -(double)S.n + W * (double)nb;
        double dE = nE - E;
        if (dE <= 0 || urand() < exp(-dE / T)) {
            E = nE;
            bad = nb;
            if (nb == 0 && S.n > best_n) {
                copy_state(&BEST, &S);
                best_n = S.n;
                since = 0;
            }
        } else {
            copy_state(&S, &B);
        }

        since++;
        if (since > 3000) {
            copy_state(&S, &BEST);
            bad = 0;
            E = -(double)S.n;
            since = 0;
        }
    }

    int bn = BEST.n;
    long long me = 0;
    for (int u = 0; u < bn; u++)
        for (int k = 0; k < BEST.deg[u]; k++)
            if (BEST.adj[u][k] > u) me++;
    printf("%d %lld\n", bn, me);
    for (int u = 0; u < bn; u++)
        for (int k = 0; k < BEST.deg[u]; k++)
            if (BEST.adj[u][k] > u) printf("%d %d\n", u, BEST.adj[u][k]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with deletions.
#
# Start from the incidence graph of PG(2, q). Optionally delete a matching R of
# incidences, which frees one slot on its point and its line. SA points get a
# new vertex joined to the q+1 lines through them (capacitated per line), and
# SB lines get a new vertex joined to the q+1 points on them (capacitated per
# point). Every candidate is validated with lib.is_valid.
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
    """True if every target t is hit by <= caps[t] elements of S."""
    load = [0] * len(caps)
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(len(caps)))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy capacitated set."""
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
    """Best capacitated set from greedy, supplied seeds, then local search."""
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
    """Random matching of up to r PG incidences, as (point, line) pairs."""
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
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
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
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs[trial] if trial < len(rs) else rng.choice(rs)
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


# ----------------------------------------------------------------------------
# Driver: arc-extension construction, then C annealing from the best graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if lib.moore_bound(d, D) <= best_n:
        return best

    # Stage 1: arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        arc_deadline = start + 0.3 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            if n_c > best_n:
                consider(n_c, e_c)

    # Stage 2: simulated annealing in C, starting from the best valid graph.
    remaining = end - time.monotonic() - 3.0
    if remaining > 2.0 and best_n < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.5, 2)],
                             stdin_graph=best, timeout=remaining)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
