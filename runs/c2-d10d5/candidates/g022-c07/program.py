"""Bold variant: general-graph growth search instead of bi-Cayley lifts.

Start graph: the best exact construction (PG(2,q) or W(q) incidence graph),
or K_{d,d} as the safe fallback. The C engine then grows the graph by
inserting vertex pairs. Insertion removes d disjoint edges (a_i,b_i) and
joins x (new A vertex) to all b_i and y (new B vertex) to all a_i, so every
degree is preserved. A simulated-annealing phase of degree-preserving double
edge swaps then repairs diameter defects. Cost is the number of unreached
pairs, measured from a sampled set of sources. Sources are added whenever an
exact all-sources check finds a violation. Only exactly validated graphs are
kept, and the best one is returned.
"""
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

#define MAXD 32
#define SS 48
#define TEMP0 1.0

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int DEG, DIAM, CAP, n, nA, nB, S;
static double TL, tstart;
static int *adj, *dg, *side, *listA, *listB, *queue_;
static int *bdg, *badj;
static int bn, bnA, bnB;
static uint32_t *mark;
static uint32_t stamp;
static int src[SS];

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int has_nb(int u, int v) {
    for (int i = 0; i < dg[u]; i++)
        if (adj[u * DEG + i] == v) return 1;
    return 0;
}

static void replace_nb(int u, int old, int nw) {
    for (int i = 0; i < dg[u]; i++) {
        if (adj[u * DEG + i] == old) {
            adj[u * DEG + i] = nw;
            return;
        }
    }
}

/* Swap: (a,b),(c,e) -> (a,e),(c,b). Applying it twice with the same
   arguments restores the original graph. */
static void apply_swap(int a, int k, int c, int j) {
    int x = adj[a * DEG + k];
    int y = adj[c * DEG + j];
    adj[a * DEG + k] = y;
    adj[c * DEG + j] = x;
    replace_nb(x, a, c);
    replace_nb(y, c, a);
}

/* Number of vertices NOT within distance DIAM of s. */
static int unreached_from(int s) {
    stamp++;
    if (stamp == 0) {
        memset(mark, 0, sizeof(uint32_t) * (size_t)CAP);
        stamp = 1;
    }
    int tail = 1, fs = 0, fe = 1;
    queue_[0] = s;
    mark[s] = stamp;
    for (int dep = 0; dep < DIAM && fs < fe; dep++) {
        for (int i = fs; i < fe; i++) {
            int u = queue_[i];
            int du = dg[u];
            for (int k = 0; k < du; k++) {
                int v = adj[u * DEG + k];
                if (mark[v] != stamp) {
                    mark[v] = stamp;
                    queue_[tail++] = v;
                }
            }
        }
        fs = fe;
        fe = tail;
    }
    return n - tail;
}

static int64_t sample_cost(void) {
    int64_t c = 0;
    for (int i = 0; i < S; i++) c += unreached_from(src[i]);
    return c;
}

static void sample_reset(void) {
    S = n < SS ? n : SS;
    for (int i = 0; i < S; i++) src[i] = rndint(n);
}

static void sample_add(int v) {
    if (S <= 0) return;
    src[rndint(S)] = v;
}

/* Exact check over all sources. Returns number of violating sources and
   adds a few of them to the sample. */
static int full_check(void) {
    int bad = 0, added = 0;
    for (int s = 0; s < n; s++) {
        if (unreached_from(s) > 0) {
            bad++;
            if (added < 4) {
                sample_add(s);
                added++;
            }
        }
    }
    return bad;
}

/* Insert a new A vertex x = n and a new B vertex y = n+1 of degree DEG. */
static int insert_pair(void) {
    int as[MAXD], ks[MAXD], bs[MAXD];
    if (nA < DEG || nB < 1 || n + 2 > CAP) return 0;
    int cnt = 0, guard = 0;
    while (cnt < DEG && guard < 400) {
        guard++;
        int a = listA[rndint(nA)];
        if (dg[a] == 0) continue;
        int k = rndint(dg[a]);
        int b = adj[a * DEG + k];
        int bad = 0;
        for (int q = 0; q < cnt; q++) {
            if (as[q] == a || bs[q] == b) {
                bad = 1;
                break;
            }
        }
        if (bad) continue;
        as[cnt] = a;
        ks[cnt] = k;
        bs[cnt] = b;
        cnt++;
    }
    if (cnt < DEG) return 0;

    int x = n, y = n + 1;
    n += 2;
    side[x] = 0;
    side[y] = 1;
    listA[nA++] = x;
    listB[nB++] = y;
    dg[x] = DEG;
    dg[y] = DEG;
    for (int i = 0; i < DEG; i++) {
        int a = as[i], b = bs[i];
        adj[a * DEG + ks[i]] = y;
        adj[y * DEG + i] = a;
        replace_nb(b, a, x);
        adj[x * DEG + i] = b;
    }
    sample_add(x);
    sample_add(y);
    return 1;
}

/* Degree-preserving annealing on sampled cost. Returns 1 iff the graph is
   verified exactly valid. */
static int anneal(int maxm) {
    int64_t cost = sample_cost();
    for (int t = 0; t < maxm; t++) {
        if (cost == 0) {
            if (full_check() == 0) return 1;
            cost = sample_cost();
            continue;
        }
        if ((t & 127) == 0 && elapsed() > TL) return 0;
        if (nA < 2) return 0;
        int a = listA[rndint(nA)];
        if (dg[a] == 0) continue;
        int c = listA[rndint(nA)];
        if (c == a || dg[c] == 0) continue;
        int k = rndint(dg[a]);
        int j = rndint(dg[c]);
        int b = adj[a * DEG + k];
        int e = adj[c * DEG + j];
        if (b == e || has_nb(a, e) || has_nb(c, b)) continue;
        apply_swap(a, k, c, j);
        int64_t nc = sample_cost();
        int64_t delta = nc - cost;
        if (delta <= 0) {
            cost = nc;
        } else {
            double T = TEMP0 * (1.0 - (double)t / maxm) + 0.05;
            if (rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                apply_swap(a, k, c, j);
            }
        }
    }
    if (cost == 0) return full_check() == 0;
    return 0;
}

static void save_best(void) {
    bn = n;
    bnA = nA;
    bnB = nB;
    memcpy(bdg, dg, sizeof(int) * (size_t)n);
    memcpy(badj, adj, sizeof(int) * (size_t)n * DEG);
}

static void restore_best(void) {
    n = bn;
    nA = bnA;
    nB = bnB;
    memcpy(dg, bdg, sizeof(int) * (size_t)n);
    memcpy(adj, badj, sizeof(int) * (size_t)n * DEG);
    sample_reset();
}

static void print_best(void) {
    int m = 0;
    for (int u = 0; u < bn; u++)
        if (side[u] == 0) m += bdg[u];
    printf("%d %d\n", bn, m);
    for (int u = 0; u < bn; u++) {
        if (side[u] != 0) continue;
        for (int k = 0; k < bdg[u]; k++)
            printf("%d %d\n", u, badj[u * DEG + k]);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    CAP = atoi(argv[5]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DEG > MAXD || DIAM < 2 || CAP < 4) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > CAP || m0 < 0) {
        printf("0 0\n");
        return 0;
    }

    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    dg = calloc((size_t)CAP, sizeof(int));
    side = malloc(sizeof(int) * (size_t)CAP);
    listA = malloc(sizeof(int) * (size_t)CAP);
    listB = malloc(sizeof(int) * (size_t)CAP);
    queue_ = malloc(sizeof(int) * (size_t)CAP);
    bdg = malloc(sizeof(int) * (size_t)CAP);
    badj = malloc(sizeof(int) * (size_t)CAP * DEG);
    mark = calloc((size_t)CAP, sizeof(uint32_t));
    if (!adj || !dg || !side || !listA || !listB || !queue_ || !bdg || !badj || !mark) {
        printf("0 0\n");
        return 0;
    }
    stamp = 0;

    n = n0;
    int ok = 1;
    for (int s = 0; s < n; s++) side[s] = -1;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || dg[u] >= DEG || dg[v] >= DEG ||
            has_nb(u, v)) {
            ok = 0;
            break;
        }
        adj[u * DEG + dg[u]++] = v;
        adj[v * DEG + dg[v]++] = u;
    }

    /* bipartition by BFS */
    for (int s = 0; s < n && ok; s++) {
        if (side[s] >= 0) continue;
        int h = 0, t = 0;
        queue_[t++] = s;
        side[s] = 0;
        while (h < t && ok) {
            int u = queue_[h++];
            for (int k = 0; k < dg[u]; k++) {
                int v = adj[u * DEG + k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    queue_[t++] = v;
                } else if (side[v] == side[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    nA = nB = 0;
    for (int s = 0; s < n; s++) {
        if (side[s] == 0) listA[nA++] = s;
        else listB[nB++] = s;
    }
    if (nA == 0 || nB == 0) {
        printf("0 0\n");
        return 0;
    }

    /* the start graph must be exactly valid, otherwise report nothing */
    for (int s = 0; s < n; s++) {
        if (unreached_from(s) > 0) {
            printf("0 0\n");
            return 0;
        }
    }

    sample_reset();
    save_best();

    int batch = 1, fails = 0;
    while (elapsed() < TL) {
        if (n + 2 * batch > CAP) {
            batch = (CAP - n) / 2;
            if (batch < 1) break;
        }
        int ins = 0;
        for (int b = 0; b < batch; b++) {
            if (insert_pair()) ins++;
            else break;
        }
        if (ins == 0) {
            if (++fails > 200) break;
            continue;
        }
        fails = 0;
        int maxm = 1000 + 100 * ins;
        if (anneal(maxm)) {
            save_best();
            if (batch < 64) batch *= 2;
        } else {
            restore_best();
            if (elapsed() >= TL) break;
            if (batch > 1) batch /= 2;
        }
    }

    print_best();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Main build: exact start, then the growth engine, then exact validation.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, which is d-regular bipartite with diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 2 and D >= 3:
        remaining = time_limit - (time.monotonic() - t0)
        budget = min(0.85 * time_limit, remaining - 8.0)
        cap = min(lib.moore_bound(d, D), 20000)
        if budget > 2.0 and cap > best_n + 2:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, int(seed) & 0x7FFFFFFF, round(budget, 2), cap],
                                 stdin_graph=best,
                                 timeout=budget + 15.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
