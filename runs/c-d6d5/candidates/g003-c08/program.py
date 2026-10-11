"""Two-stage search for large bipartite graphs with max degree d and diameter D.

Stage 1 keeps the group-voltage lift annealer (Z_m x| Z_k) and the algebraic fallbacks
(projective plane incidence, generalized quadrangle W(q)). It produces a valid start graph.

Stage 2 is a different construction. It starts from a d-regular bipartite graph and grows it
by vertex-pair insertion: pick d disjoint edges (a_i, b_i), delete them, add a new A-vertex x
joined to all b_i and a new B-vertex y joined to all a_i. Every degree is preserved. The
inserted vertices usually break the diameter bound, so a degree-preserving 2-switch annealer
(bitset BFS cost = number of pairs at distance > D) repairs the graph. A failed repair rolls
back to the last valid snapshot. Python validates every result and keeps a safe fallback.
"""
import itertools
import math
import random
import time

import lib


C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDARTS 512
#define MAXKB 8

static int dd, DD, kb, mm, kk, rr, G, NV;
static int *MT;
static int nd;
static int dI[MAXDARTS], dJ[MAXDARTS], dS[MAXDARTS];
static int bJ[MAXDARTS], bS[MAXDARTS];
static int *adj, *stampv, *cnt, *fr1, *fr2;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t next_rand(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rand_int(int n) { return (int)(next_rand() % (uint64_t)n); }

static double rand_unit(void) {
    return (double)(next_rand() >> 11) * (1.0 / 9007199254740992.0);
}

static void build_group(void) {
    int *pw = malloc(sizeof(int) * kk);
    pw[0] = 1 % mm;
    for (int b = 1; b < kk; b++) pw[b] = (pw[b - 1] * rr) % mm;
    G = mm * kk;
    MT = malloc(sizeof(int) * G * G);
    for (int x = 0; x < G; x++) {
        int a = x / kk, b = x % kk;
        for (int y = 0; y < G; y++) {
            int c = y / kk, e = y % kk;
            int aa = (a + (pw[b] * c) % mm) % mm;
            int bb = (b + e) % kk;
            MT[x * G + y] = aa * kk + bb;
        }
    }
    free(pw);
}

static void build_adj(void) {
    for (int v = 0; v < NV; v++) cnt[v] = 0;
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t], s = dS[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (kb + j) * G + MT[g * G + s];
            if (cnt[a] < dd) adj[a * dd + cnt[a]] = b;
            cnt[a]++;
            if (cnt[b] < dd) adj[b * dd + cnt[b]] = a;
            cnt[b]++;
        }
    }
}

/* Number of (representative, vertex) pairs at distance > DD. Zero means valid. */
static long long cost_fn(void) {
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2])
                return 1000000000LL;
    build_adj();
    long long total = 0;
    int nreps = 2 * kb;
    for (int q = 0; q < nreps; q++) {
        int src = q * G;
        if (stamp >= 0x7ffffff0) {
            memset(stampv, 0, sizeof(int) * NV);
            stamp = 0;
        }
        stamp++;
        int *fr = fr1, *nx = fr2;
        int nf = 1;
        fr[0] = src;
        stampv[src] = stamp;
        int reached = 1;
        for (int lvl = 0; lvl < DD && nf > 0; lvl++) {
            int nn = 0;
            for (int x = 0; x < nf; x++) {
                int u = fr[x];
                for (int k = 0; k < dd; k++) {
                    int w = adj[u * dd + k];
                    if (stampv[w] != stamp) {
                        stampv[w] = stamp;
                        nx[nn++] = w;
                    }
                }
            }
            reached += nn;
            int *tmp = fr;
            fr = nx;
            nx = tmp;
            nf = nn;
        }
        total += NV - reached;
    }
    return total;
}

static void print_best(void) {
    memcpy(dJ, bJ, sizeof(int) * nd);
    memcpy(dS, bS, sizeof(int) * nd);
    printf("%d %d\n", NV, nd * G);
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t], s = dS[t];
        for (int g = 0; g < G; g++)
            printf("%d %d\n", i * G + g, (kb + j) * G + MT[g * G + s]);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: d D seed time m k r kb\n");
        return 1;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    mm = atoi(argv[5]);
    kk = atoi(argv[6]);
    rr = atoi(argv[7]);
    kb = atoi(argv[8]);
    if (dd < 1 || dd > 64 || DD < 1 || kb < 1 || kb > MAXKB || mm < 2 || kk < 1 || rr < 0) {
        printf("0 0\n");
        return 0;
    }
    nd = dd * kb;
    if (nd > MAXDARTS) {
        printf("0 0\n");
        return 0;
    }
    build_group();
    NV = 2 * kb * G;
    if (NV > 200000) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    adj = malloc(sizeof(int) * NV * dd);
    stampv = calloc(NV, sizeof(int));
    cnt = malloc(sizeof(int) * NV);
    fr1 = malloc(sizeof(int) * NV);
    fr2 = malloc(sizeof(int) * NV);

    /* Initial state: one random permutation per layer, random voltages. */
    int perm[MAXKB];
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rand_int(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < kb; i++) {
            dI[l * kb + i] = i;
            dJ[l * kb + i] = perm[i];
            dS[l * kb + i] = rand_int(G);
        }
    }

    long long cur = cost_fn();
    long long best = cur;
    memcpy(bJ, dJ, sizeof(int) * nd);
    memcpy(bS, dS, sizeof(int) * nd);

    clock_t c0 = clock();
    const double T0 = 3.0;
    long long it = 0;
    double frac = 0.0;
    while (best > 0) {
        if ((it & 63) == 0) {
            frac = (double)(clock() - c0) / CLOCKS_PER_SEC / tl;
            if (frac >= 1.0) break;
        }
        it++;
        double T = T0 * (1.0 - frac) + 0.05;
        int undoSwap = 0;
        int u1 = 0, u2 = 0, oldv = 0;
        if (kb >= 2 && rand_int(4) == 0) {
            int l = rand_int(dd);
            int i1 = rand_int(kb);
            int i2 = rand_int(kb - 1);
            if (i2 >= i1) i2++;
            u1 = l * kb + i1;
            u2 = l * kb + i2;
            int tmp = dJ[u1];
            dJ[u1] = dJ[u2];
            dJ[u2] = tmp;
            undoSwap = 1;
        } else {
            u1 = rand_int(nd);
            oldv = dS[u1];
            dS[u1] = rand_int(G);
        }
        long long c2 = cost_fn();
        int accept = (c2 <= cur);
        if (!accept) {
            double p = exp(-(double)(c2 - cur) / T);
            accept = (rand_unit() < p);
        }
        if (accept) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bJ, dJ, sizeof(int) * nd);
                memcpy(bS, dS, sizeof(int) * nd);
            }
        } else {
            if (undoSwap) {
                int tmp = dJ[u1];
                dJ[u1] = dJ[u2];
                dJ[u2] = tmp;
            } else {
                dS[u1] = oldv;
            }
        }
    }

    if (best == 0) print_best();
    else printf("0 0\n");
    return 0;
}
"""


C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 1200
#define WMAX ((2 * CAP + 63) / 64)
#define MAXFAIL 4

/* Bipartite graph with sides A (indices 0..N-1) and B (indices 0..N-1), d-regular.
   aA[a*d+k] = b-index of k-th neighbour of a; aB[b*d+k] = a-index of k-th neighbour of b. */
static int d, D, N, snapN;
static int *aA, *aB, *sA, *sB, *usedA, *usedB;
static uint64_t *RA, *RB, *TA, *TB;
static int W;
static uint64_t rs = 88172645463325252ULL;
static double deadline;
static const double T0 = 1.5;
static int ua1, uk1, ua2, uk2, ub1, ub2, usb1, usb2;

static uint64_t next_rand(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rand_int(int n) { return (int)(next_rand() % (uint64_t)n); }

static double rand_unit(void) {
    return (double)(next_rand() >> 11) * (1.0 / 9007199254740992.0);
}

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_in(const int *arr, int cnt, int want) {
    for (int k = 0; k < cnt; k++)
        if (arr[k] == want) return k;
    return -1;
}

/* Number of unordered pairs at distance > D. Zero means valid. */
static long long evaluate(void) {
    int n2 = 2 * N;
    W = (n2 + 63) / 64;
    size_t bytes = sizeof(uint64_t) * (size_t)N * (size_t)W;
    memset(RA, 0, bytes);
    memset(RB, 0, bytes);
    for (int a = 0; a < N; a++) RA[(size_t)a * W + (a >> 6)] |= 1ULL << (a & 63);
    for (int b = 0; b < N; b++) {
        int id = N + b;
        RB[(size_t)b * W + (id >> 6)] |= 1ULL << (id & 63);
    }
    uint64_t *xa = RA, *xb = RB, *ya = TA, *yb = TB;
    for (int r = 0; r < D; r++) {
        for (int a = 0; a < N; a++) {
            uint64_t *dst = ya + (size_t)a * W;
            memcpy(dst, xa + (size_t)a * W, sizeof(uint64_t) * W);
            const int *nb = aA + (size_t)a * d;
            for (int k = 0; k < d; k++) {
                const uint64_t *s = xb + (size_t)nb[k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        for (int b = 0; b < N; b++) {
            uint64_t *dst = yb + (size_t)b * W;
            memcpy(dst, xb + (size_t)b * W, sizeof(uint64_t) * W);
            const int *nb = aB + (size_t)b * d;
            for (int k = 0; k < d; k++) {
                const uint64_t *s = xa + (size_t)nb[k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = xa;
        xa = ya;
        ya = t;
        t = xb;
        xb = yb;
        yb = t;
    }
    long long sum = 0;
    for (int a = 0; a < N; a++) {
        const uint64_t *s = xa + (size_t)a * W;
        for (int w = 0; w < W; w++) sum += popc(s[w]);
    }
    for (int b = 0; b < N; b++) {
        const uint64_t *s = xb + (size_t)b * W;
        for (int w = 0; w < W; w++) sum += popc(s[w]);
    }
    long long total = (long long)n2 * n2;
    return (total - sum) / 2;
}

/* Degree-preserving 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). */
static int try_switch(void) {
    int a1 = rand_int(N), a2 = rand_int(N);
    if (a1 == a2) return 0;
    int k1 = rand_int(d), k2 = rand_int(d);
    int b1 = aA[a1 * d + k1], b2 = aA[a2 * d + k2];
    if (b1 == b2) return 0;
    if (find_in(aA + (size_t)a1 * d, d, b2) >= 0) return 0;
    if (find_in(aA + (size_t)a2 * d, d, b1) >= 0) return 0;
    int sb1 = find_in(aB + (size_t)b1 * d, d, a1);
    int sb2 = find_in(aB + (size_t)b2 * d, d, a2);
    if (sb1 < 0 || sb2 < 0) return 0;
    aA[a1 * d + k1] = b2;
    aA[a2 * d + k2] = b1;
    aB[b1 * d + sb1] = a2;
    aB[b2 * d + sb2] = a1;
    ua1 = a1; uk1 = k1; ua2 = a2; uk2 = k2;
    ub1 = b1; ub2 = b2; usb1 = sb1; usb2 = sb2;
    return 1;
}

static void undo_switch(void) {
    aA[ua1 * d + uk1] = ub1;
    aA[ua2 * d + uk2] = ub2;
    aB[ub1 * d + usb1] = ua1;
    aB[ub2 * d + usb2] = ua2;
}

/* Insert a new A-vertex x = N and B-vertex y = N, using d disjoint edges (a_i, b_i). */
static int grow(void) {
    if (N + 1 > CAP) return 0;
    int ma[64], mb[64];
    int cnt = 0;
    memset(usedA, 0, sizeof(int) * N);
    memset(usedB, 0, sizeof(int) * N);
    int tries = 0;
    while (cnt < d && tries < 10000) {
        tries++;
        int a = rand_int(N);
        if (usedA[a]) continue;
        int k = rand_int(d);
        int b = aA[a * d + k];
        if (usedB[b]) continue;
        usedA[a] = 1;
        usedB[b] = 1;
        ma[cnt] = a;
        mb[cnt] = b;
        cnt++;
    }
    if (cnt < d) return 0;
    int x = N, y = N;
    for (int i = 0; i < d; i++) {
        int a = ma[i], b = mb[i];
        int sa = find_in(aA + (size_t)a * d, d, b);
        int sbb = find_in(aB + (size_t)b * d, d, a);
        aA[a * d + sa] = y;
        aB[b * d + sbb] = x;
        aA[x * d + i] = b;
        aB[y * d + i] = a;
    }
    N++;
    return 1;
}

static void take_snapshot(void) {
    snapN = N;
    memcpy(sA, aA, sizeof(int) * (size_t)N * d);
    memcpy(sB, aB, sizeof(int) * (size_t)N * d);
}

static void restore_snapshot(void) {
    N = snapN;
    memcpy(aA, sA, sizeof(int) * (size_t)N * d);
    memcpy(aB, sB, sizeof(int) * (size_t)N * d);
}

static long long anneal(double stage_end) {
    long long cur = evaluate();
    double t_begin = now();
    double span = stage_end - t_begin;
    if (span < 1e-3) span = 1e-3;
    double frac = 0.0;
    long long it = 0;
    while (cur > 0) {
        if ((it & 31) == 0) {
            double tn = now();
            if (tn >= stage_end || tn >= deadline) break;
            frac = (tn - t_begin) / span;
        }
        it++;
        double T = T0 * (1.0 - frac) + 0.05;
        if (!try_switch()) continue;
        long long c2 = evaluate();
        if (c2 <= cur || rand_unit() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            undo_switch();
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: d D seed time\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int n = 0, m = 0;
    if (d < 1 || d > 16 || D < 1 || scanf("%d %d", &n, &m) != 2 || n < 2 || (n % 2) ||
        m != (n / 2) * d || n / 2 > CAP) {
        printf("0 0\n");
        return 0;
    }
    N = n / 2;
    aA = malloc(sizeof(int) * (size_t)CAP * d);
    aB = malloc(sizeof(int) * (size_t)CAP * d);
    sA = malloc(sizeof(int) * (size_t)CAP * d);
    sB = malloc(sizeof(int) * (size_t)CAP * d);
    usedA = malloc(sizeof(int) * CAP);
    usedB = malloc(sizeof(int) * CAP);
    RA = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    RB = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    TA = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    TB = malloc(sizeof(uint64_t) * (size_t)CAP * WMAX);
    int *ca = calloc(N, sizeof(int));
    int *cb = calloc(N, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || u >= N || v < N || v >= n) {
            printf("0 0\n");
            return 0;
        }
        int a = u, b = v - N;
        if (ca[a] >= d || cb[b] >= d) {
            printf("0 0\n");
            return 0;
        }
        aA[a * d + ca[a]++] = b;
        aB[b * d + cb[b]++] = a;
    }
    for (int a = 0; a < N; a++)
        for (int i = 0; i < d; i++)
            for (int j = i + 1; j < d; j++)
                if (aA[a * d + i] == aA[a * d + j]) {
                    printf("0 0\n");
                    return 0;
                }

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    deadline = now() + tl;

    long long cur = anneal(deadline);
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    take_snapshot();
    int fails = 0;
    while (fails < MAXFAIL) {
        double remaining = deadline - now();
        if (remaining < 0.2) break;
        if (!grow()) {
            fails++;
            continue;
        }
        double stage = remaining * 0.35;
        if (stage < 1.5) stage = remaining;
        long long c = anneal(now() + stage);
        if (c == 0) {
            take_snapshot();
            fails = 0;
        } else {
            restore_snapshot();
            fails++;
        }
    }

    printf("%d %d\n", 2 * N, N * d);
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", a, N + aA[a * d + k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Algebraic fallbacks.
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
# Group selection and C drivers.
# ----------------------------------------------------------------------------

def _groups(G):
    """All semidirect factorizations (m, k, r) with m*k = G, m >= 2, r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _run_c_search(d, D, seed, secs, m, k, r, kb):
    """Run the group-lift annealer for one group and base size. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_LIFT, [d, D, seed, f"{secs:.2f}", m, k, r, kb],
                        timeout=secs + 5.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    return n, e


def _as_regular_bipartite(n, edges, d):
    """Relabel a d-regular bipartite graph to A = 0..N-1, B = N..2N-1. Returns (n, edges) or None."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    if n < 2 or any(x != d for x in deg):
        return None
    adj = lib.adjacency(n, edges)
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
                elif color[v] == color[u]:
                    return None
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if len(A) != len(B) or not A:
        return None
    N = len(A)
    ida = {v: i for i, v in enumerate(A)}
    idb = {v: N + i for i, v in enumerate(B)}
    out = []
    for u, v in edges:
        if color[u] == 0:
            out.append((ida[u], idb[v]))
        else:
            out.append((ida[v], idb[u]))
    return 2 * N, out


def _grow_search(d, D, seed, secs, start):
    """Run the insertion-and-repair annealer from a regular bipartite start. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_GROW, [d, D, seed, f"{secs:.2f}"], stdin_graph=start,
                        timeout=secs + 8.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + max(1.0, 0.8 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if d <= 2 or best_n >= moore:
        return best

    # Stage 1: group-voltage lifts give a strong valid start.
    rng = random.Random(seed)
    lift_end = t0 + 0.4 * (end - t0)
    trial = 0
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 2.0:
            break
        secs = min(4.0, remaining - 0.5)
        kb = rng.choice([1, 1, 1, 2, 2, 3])
        G = best_n // (2 * kb) + 1 + rng.randrange(0, 10)
        groups = _groups(G)
        while not groups:
            G += 1
            groups = _groups(G)
        nonab = [g for g in groups if g[1] > 1 and g[2] != 1]
        if nonab and rng.random() < 0.7:
            m, k, r = rng.choice(nonab)
        else:
            m, k, r = rng.choice(groups)
        res = _run_c_search(d, D, seed * 7919 + trial, secs, m, k, r, kb)
        trial += 1
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best = res
            best_n = res[0]
        if best_n >= moore:
            break

    # Stage 2: grow by vertex-pair insertion and repair by degree-preserving switches.
    if best_n < moore and time.monotonic() < end - 3.0:
        start = _as_regular_bipartite(best[0], best[1], d)
        if start is not None:
            rem = end - time.monotonic() - 1.0
            res = _grow_search(d, D, seed, rem, start)
            if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
                best = res
                best_n = res[0]

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
