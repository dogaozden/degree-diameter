"""Grow-and-repair search for bipartite graphs with max degree d and diameter D.

Start from the best algebraic construction available: the Araujo-Pardo-Lopez graph
when d-2 is a prime power, otherwise the PG(2,q) incidence graph. The C engine then
repeatedly adds one vertex on a random side and repairs the graph by simulated
annealing over degree-preserving edge moves. The cost is the number of vertex pairs
at distance > D, computed with bitset balls. A state with cost 0 is a valid graph,
so every such state is recorded and the largest one is returned.
"""
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1100
#define DMAX 40
#define EMAX (NMAX * DMAX / 2 + 64)
#define WMAX ((NMAX + 63) / 64)
#define LOGMAX 16
#define ITER_ROUND 200000L

typedef struct { int type, a, b; } Op;

static int dl, D, n, ecount;
static int col[NMAX], deg[NMAX], nb[NMAX][DMAX];
static int eidx[NMAX][NMAX];
static int eu[EMAX], ev[EMAX];
static int spA[NMAX], spB[NMAX];
static uint64_t B1[NMAX][WMAX], B2[NMAX][WMAX];
static Op logv[LOGMAX];
static int logn;
static int bestn, bestm, have_best;
static int bestEu[EMAX], bestEv[EMAX], bestcol[NMAX];
static double deadline_s;
static uint64_t rs = 88172645463325252ULL;
static int iu[EMAX], iv[EMAX];
static int qbuf[NMAX];

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---- raw graph edit: eu[] is always the colour-0 endpoint ---- */

static void add_raw(int a, int b) {
    int id = ecount++;
    eu[id] = a;
    ev[id] = b;
    eidx[a][b] = eidx[b][a] = id + 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rem_nb(int v, int w) {
    for (int k = 0; k < deg[v]; k++) {
        if (nb[v][k] == w) {
            nb[v][k] = nb[v][deg[v] - 1];
            deg[v]--;
            return;
        }
    }
}

static void del_raw(int a, int b) {
    int id = eidx[a][b] - 1;
    int last = ecount - 1;
    if (id != last) {
        int ua = eu[last], vb = ev[last];
        eu[id] = ua;
        ev[id] = vb;
        eidx[ua][vb] = eidx[vb][ua] = id + 1;
    }
    ecount--;
    eidx[a][b] = eidx[b][a] = 0;
    rem_nb(a, b);
    rem_nb(b, a);
}

static void op_add(int a, int b) {
    add_raw(a, b);
    logv[logn].type = 1;
    logv[logn].a = a;
    logv[logn].b = b;
    logn++;
}

static void op_del(int a, int b) {
    del_raw(a, b);
    logv[logn].type = 0;
    logv[logn].a = a;
    logv[logn].b = b;
    logn++;
}

static void undo_all(void) {
    while (logn > 0) {
        logn--;
        Op o = logv[logn];
        if (o.type == 1) del_raw(o.a, o.b);
        else add_raw(o.a, o.b);
    }
}

static void clear_graph(void) {
    for (int i = 0; i < ecount; i++) {
        eidx[eu[i]][ev[i]] = 0;
        eidx[ev[i]][eu[i]] = 0;
    }
    for (int v = 0; v < n; v++) deg[v] = 0;
    ecount = 0;
}

static void save_best(void) {
    bestn = n;
    bestm = ecount;
    for (int i = 0; i < ecount; i++) {
        bestEu[i] = eu[i];
        bestEv[i] = ev[i];
    }
    for (int v = 0; v < n; v++) bestcol[v] = col[v];
    have_best = 1;
}

static void restore_best(void) {
    clear_graph();
    n = bestn;
    for (int v = 0; v < n; v++) col[v] = bestcol[v];
    for (int i = 0; i < bestm; i++) add_raw(bestEu[i], bestEv[i]);
}

/* Number of unordered vertex pairs at distance > D (0 iff valid). */
static long long cost_fn(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = B1, (*nxt)[WMAX] = B2, (*tmp)[WMAX];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[nb[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* One random move: add a pair of spare vertices if possible, else an endpoint
   move (edge endpoint moved to a spare vertex) or a degree-preserving double swap. */
static int try_move(void) {
    int nsA = 0, nsB = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dl) {
            if (col[v] == 0) spA[nsA++] = v;
            else spB[nsB++] = v;
        }
    }
    if (nsA && nsB) {
        for (int t = 0; t < 8; t++) {
            int c = spA[rnd() % nsA], b = spB[rnd() % nsB];
            if (!eidx[c][b]) {
                op_add(c, b);
                return 1;
            }
        }
    }
    if (ecount == 0) return 0;
    int i = (int)(rnd() % ecount);
    int a = eu[i], b = ev[i];
    int r = (int)(rnd() % 100);
    if (r < 35) {
        if (nsA) {
            int c = spA[rnd() % nsA];
            if (c != a && !eidx[c][b]) {
                op_del(a, b);
                op_add(c, b);
                return 1;
            }
        }
    } else if (r < 70) {
        if (nsB) {
            int e = spB[rnd() % nsB];
            if (e != b && !eidx[a][e]) {
                op_del(a, b);
                op_add(a, e);
                return 1;
            }
        }
    } else if (ecount >= 2) {
        int j = (int)(rnd() % ecount);
        int c = eu[j], e = ev[j];
        if (j != i && a != c && b != e && !eidx[a][e] && !eidx[c][b]) {
            op_del(a, b);
            op_del(c, e);
            op_add(a, e);
            op_add(c, b);
            return 1;
        }
    }
    return 0;
}

/* Simulated annealing on the current graph; returns the final cost. */
static long long anneal(long iters) {
    long long cur = cost_fn();
    const double T0 = 2.0, T1 = 0.05;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now() > deadline_s) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        logn = 0;
        if (!try_move()) {
            logn = 0;
            continue;
        }
        long long c = cost_fn();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) cur = c;
        else undo_all();
        logn = 0;
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dl = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    deadline_s = now() + budget;
    if (dl < 2 || dl > DMAX || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || n0 > NMAX - 2 || m0 < 0 || m0 > EMAX - 1) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }

    if (n0 == 0) {
        n = 2 * dl;
        for (int v = 0; v < n; v++) col[v] = (v < dl) ? 0 : 1;
        for (int a = 0; a < dl; a++)
            for (int b = 0; b < dl; b++) add_raw(a, dl + b);
    } else {
        n = n0;
        for (int i = 0; i < m0; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || u >= n || v < 0 || v >= n || u == v || eidx[u][v] ||
                deg[u] >= dl || deg[v] >= dl) {
                printf("0 0\n");
                return 0;
            }
            add_raw(u, v);
        }
        for (int v = 0; v < n; v++) col[v] = -1;
        for (int s = 0; s < n; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int head = 0, tail = 0;
            qbuf[tail++] = s;
            while (head < tail) {
                int u = qbuf[head++];
                for (int k = 0; k < deg[u]; k++) {
                    int w = nb[u][k];
                    if (col[w] < 0) {
                        col[w] = 1 - col[u];
                        qbuf[tail++] = w;
                    }
                }
            }
        }
        for (int i = 0; i < ecount; i++) {
            if (col[eu[i]] == col[ev[i]]) {
                printf("0 0\n");
                return 0;
            }
        }
        int m = ecount;
        for (int i = 0; i < m; i++) {
            if (col[eu[i]] == 0) {
                iu[i] = eu[i];
                iv[i] = ev[i];
            } else {
                iu[i] = ev[i];
                iv[i] = eu[i];
            }
        }
        clear_graph();
        for (int i = 0; i < m; i++) add_raw(iu[i], iv[i]);
    }

    /* Moore bound for bipartite graphs with max degree dl and diameter D. */
    double s = 0.0, t = 1.0;
    for (int i = 0; i < D; i++) {
        s += t;
        t *= (double)(dl - 1);
    }
    double moore = 2.0 * s;

    if (cost_fn() == 0) save_best();
    while (now() < deadline_s) {
        if (!have_best) {
            long long c = anneal(ITER_ROUND);
            if (c == 0) save_best();
            continue;
        }
        if ((double)(n + 1) > moore || n + 1 >= NMAX) break;
        int side = (int)(rnd() & 1);
        col[n] = side;
        deg[n] = 0;
        n++;
        long long c = anneal(ITER_ROUND);
        if (c == 0) save_best();
        else restore_best();
    }

    if (have_best) {
        printf("%d %d\n", bestn, bestm);
        for (int i = 0; i < bestm; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ---------------------------------------------------------------- constructions

def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    return lib.projective_plane_incidence(q) if q >= 2 else None


def _al_base(d):
    """Araujo-Pardo-Lopez graph for degree d = q+2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    return lib.araujo_lopez_graph(q)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    if d >= 3:
        pg = _pg_base(d)
        if pg is not None:
            if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal, nothing to improve
                return _finish(cands + [pg], d, D)
            cands.append(pg)

    try:
        al = _al_base(d) if D >= 3 else None
    except Exception:
        al = None
    if al is not None:
        cands.append(al)

    start = _finish(cands, d, D)
    best_n, best_e = start

    # Grow-and-repair search in C, using the remaining budget.
    elapsed = time.monotonic() - t0
    budget = 0.8 * time_limit - elapsed - 2.0
    if budget >= 1.0 and best_n >= 2:
        timeout = min(time_limit - elapsed - 1.0, budget + 5.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=(best_n, best_e), timeout=timeout)
            n2, e2 = lib.parse_graph_text(text)
            if n2 > best_n and lib.is_valid(n2, e2, d, D):
                cands.append((n2, e2))
        except Exception:
            pass

    return _finish(cands, d, D)
