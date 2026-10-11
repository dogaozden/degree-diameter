"""Diameter-3 bipartite search: clone packing on projective-plane starts, then C augmentation.

Starts are PG(2,q) incidence graphs, Araujo-Pardo-Lopez graphs, and (for D >= 4) the
generalized quadrangle W(q). A clone of an old vertex v is a new vertex on v's side with v's
neighbourhood. Cloning the points of PG(2,q) uses the spare degree on the lines, and the
clone graph keeps diameter 3 for any choice of clones. Each side is packed independently by
penalised simulated annealing, which is a (k,s)-arc search. The C engine validates the packed
graph exactly, augments greedily with set-cover attachments, and prints the best valid graph.
Python re-checks everything with lib.is_valid.
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

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64
#define LAM_LO 1.1
#define LAM_HI 1.8

static int N, N0, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static int base_deg[MAXN];
static int base_adj[MAXN][MAXDEG];
static int base_side[MAXN];
static int snap_N;
static int snap_deg[MAXN];
static int snap_adj[MAXN][MAXDEG];
static int snap_side[MAXN];

static int cap[MAXN], ld[MAXN];
static int elist[MAXN], xsel[MAXN], bestx[MAXN];
static int selA[MAXN], selB[MAXN], comb[MAXN];

static uint64_t rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnext() % (uint64_t)k); }
static double urand(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of all vertices within distance r of src. */
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

/* Add one new vertex on side X joined to a greedy set cover T of spare vertices
   on the other side. Accepted only if every existing vertex lies within Dist-1 of T. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    W = (N + 63) / 64;
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

/* Exact check: simple bipartite, degree <= Dd, diameter <= Dist. */
static int valid_graph(void) {
    uint64_t tmp[WORDS];
    if (N < 1 || N > MAXN - 2) return 0;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        if (deg[v] > Dd) return 0;
        for (int k = 0; k < deg[v]; k++)
            if (side[adj[v][k]] == side[v]) return 0;
    }
    for (int v = 0; v < N; v++) {
        ball_of(v, Dist, tmp);
        for (int i = 0; i < W; i++) {
            uint64_t want = ~0ULL;
            if (i == W - 1 && (N & 63)) want = (1ULL << (N & 63)) - 1ULL;
            if ((tmp[i] & want) != want) return 0;
        }
    }
    return 1;
}

static void restore_base(void) {
    N = N0;
    for (int v = 0; v < N0; v++) {
        deg[v] = base_deg[v];
        side[v] = base_side[v];
        memcpy(adj[v], base_adj[v], sizeof(int) * MAXDEG);
    }
}

static void save_snap(void) {
    snap_N = N;
    for (int v = 0; v < N; v++) {
        snap_deg[v] = deg[v];
        snap_side[v] = side[v];
        memcpy(snap_adj[v], adj[v], sizeof(int) * MAXDEG);
    }
}

/* Clone each source vertex (copy of its base neighbourhood, same side). */
static void add_clones(const int *src, int cnt) {
    for (int c = 0; c < cnt; c++) {
        int s = src[c];
        int x = N++;
        side[x] = base_side[s];
        deg[x] = 0;
        for (int k = 0; k < base_deg[s]; k++) {
            int w = base_adj[s][k];
            adj[x][deg[x]++] = w;
            adj[w][deg[w]++] = x;
        }
    }
}

/* Penalised annealing: choose elements e on side Y maximising the count, subject to
   each target w (other side) being hit by at most cap[w] chosen elements. */
static int pack_side(int Y, double tend, int *out) {
    int M = 0;
    for (int v = 0; v < N0; v++)
        if (base_side[v] == Y && base_deg[v] > 0) elist[M++] = v;
    int anycap = 0;
    for (int w = 0; w < N0; w++)
        if (base_side[w] != Y && cap[w] > 0) anycap = 1;
    if (M == 0 || !anycap) return 0;
    for (int i = 0; i < M; i++) bestx[i] = 0;
    int bestsz = 0;
    long iters = 100000L + 1000L * M;
    for (int rep = 0; rep < 1000000; rep++) {
        if (rep > 0 && now() >= tend) break;
        double lam = LAM_LO + (LAM_HI - LAM_LO) * urand();
        for (int w = 0; w < N0; w++) ld[w] = 0;
        for (int i = 0; i < M; i++) xsel[i] = 0;
        int size = 0, over = 0;
        double T = 0.5;
        double ratio = pow(0.02 / 0.5, 1.0 / (double)iters);
        for (long it = 0; it < iters; it++, T *= ratio) {
            int i = rndint(M);
            int e = elist[i];
            int nb = base_deg[e];
            if (!xsel[i]) {
                int viol = 0;
                for (int k = 0; k < nb; k++) {
                    int w = base_adj[e][k];
                    if (ld[w] >= cap[w]) viol++;
                }
                double df = 1.0 - lam * viol;
                if (df >= 0.0 || urand() < exp(df / T)) {
                    xsel[i] = 1;
                    size++;
                    over += viol;
                    for (int k = 0; k < nb; k++) ld[base_adj[e][k]]++;
                }
            } else {
                int viol = 0;
                for (int k = 0; k < nb; k++) {
                    int w = base_adj[e][k];
                    if (ld[w] > cap[w]) viol++;
                }
                double df = -1.0 + lam * viol;
                if (df >= 0.0 || urand() < exp(df / T)) {
                    xsel[i] = 0;
                    size--;
                    over -= viol;
                    for (int k = 0; k < nb; k++) ld[base_adj[e][k]]--;
                }
            }
            if (over == 0 && size > bestsz) {
                bestsz = size;
                for (int j = 0; j < M; j++) bestx[j] = xsel[j];
            }
        }
    }
    /* Greedy fill of the best set. */
    for (int w = 0; w < N0; w++) ld[w] = 0;
    for (int i = 0; i < M; i++) {
        if (!bestx[i]) continue;
        int e = elist[i];
        for (int k = 0; k < base_deg[e]; k++) ld[base_adj[e][k]]++;
    }
    for (int i = 0; i < M; i++) {
        if (bestx[i]) continue;
        int e = elist[i], ok = 1;
        for (int k = 0; k < base_deg[e]; k++) {
            int w = base_adj[e][k];
            if (ld[w] >= cap[w]) { ok = 0; break; }
        }
        if (ok) {
            bestx[i] = 1;
            for (int k = 0; k < base_deg[e]; k++) ld[base_adj[e][k]]++;
        }
    }
    int c = 0;
    for (int i = 0; i < M; i++)
        if (bestx[i]) out[c++] = elist[i];
    return c;
}

/* variant 0: A+B clones, 1: A only, 2: B only. Leaves the graph in that state. */
static int build_variant(int v, int nA, int nB) {
    int c = 0;
    if (v == 0 || v == 1)
        for (int i = 0; i < nA; i++) comb[c++] = selA[i];
    if (v == 0 || v == 2)
        for (int i = 0; i < nB; i++) comb[c++] = selB[i];
    restore_base();
    if (N0 + c > MAXN - 2) return -1;
    add_clones(comb, c);
    return c;
}

static void emit(int n, int (*ad)[MAXDEG], const int *dg) {
    long M = 0;
    for (int v = 0; v < n; v++)
        for (int k = 0; k < dg[v]; k++)
            if (ad[v][k] > v) M++;
    printf("%d %ld\n", n, M);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < dg[v]; k++)
            if (ad[v][k] > v) printf("%d %d\n", v, ad[v][k]);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
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
    for (int i = 0; i < 10; i++) rnext();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 200 || Dist < 1 || Dd < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    N0 = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= Dd || deg[v] >= Dd) continue;
        if (has_edge(u, v)) continue;
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

    for (int v = 0; v < N0; v++) {
        base_deg[v] = deg[v];
        base_side[v] = side[v];
        memcpy(base_adj[v], adj[v], sizeof(int) * MAXDEG);
        cap[v] = Dd - deg[v];
    }
    save_snap();

    double t0 = now();
    double tA = t0 + 0.25 * budget;
    double tB = t0 + 0.50 * budget;
    double tEnd = t0 + budget;

    int nA = pack_side(0, tA, selA);
    int nB = pack_side(1, tB, selB);

    int bestTot = 0, bestV = -1;
    int cnts[3] = {nA + nB, nA, nB};
    for (int v = 0; v < 3; v++) {
        if (cnts[v] <= bestTot) continue;
        int c = build_variant(v, nA, nB);
        if (c < 0) continue;
        if (valid_graph()) {
            bestTot = cnts[v];
            bestV = v;
        }
    }
    if (bestV >= 0) build_variant(bestV, nA, nB);
    else restore_base();
    W = (N + 63) / 64;
    save_snap();

    recompute_balls();
    int fails = 0;
    while (now() < tEnd && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    if (valid_graph()) emit(N, adj, deg);
    else emit(snap_N, snap_adj, snap_deg);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Start constructions.
# ----------------------------------------------------------------------------

def _pg_candidates(d):
    """PG(2,q) incidence graphs for prime powers q with q + 1 <= d, with a packing estimate."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        n, edges = lib.projective_plane_incidence(q)
        m = n // 2
        s = d - q - 1
        est = n + 2 * (s * m // (q + 1))
        out.append((est, n, edges))
    return out


def _araujo_candidates(d):
    """Araujo-Pardo-Lopez graphs of degree q + 2 <= d."""
    out = []
    for q in range(3, min(d - 2, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        n, edges = lib.araujo_lopez_graph(q)
        out.append((n, n, edges))
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (small q only, for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 75% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.75 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2: always valid for D >= 2 and a safe fallback.
    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        return 1, []
    best = fallback

    starts = []
    if D >= 3:
        starts.extend(sorted(_pg_candidates(d), key=lambda c: -c[0])[:2])
        starts.extend(sorted(_araujo_candidates(d), key=lambda c: -c[0])[:2])
    if D >= 4 and time.monotonic() < t0 + 0.1 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append((gq[0], gq[0], gq[1]))
    starts = [s for s in starts if lib.is_valid(s[1], s[2], d, D)]
    starts.sort(key=lambda s: -s[0])
    starts = starts[:3]
    starts.append((fallback[0], fallback[0], fallback[1]))

    weights = [0.55, 0.25, 0.12, 0.08]
    for idx, (_est, n0, e0) in enumerate(starts):
        remaining = hard_end - time.monotonic()
        if remaining < 3.0:
            break
        wsum = sum(weights[idx:len(starts)])
        share = remaining * weights[idx] / wsum
        engine_budget = max(1.0, share - 1.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 31 + idx, f"{engine_budget:.2f}"],
                             stdin_graph=(n0, e0), timeout=share + 3.0)
            n1, e1 = lib.parse_graph_text(text)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
