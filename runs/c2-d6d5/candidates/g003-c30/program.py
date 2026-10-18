import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Bipartite 2-switch annealing for bipartite d-regular graphs of diameter <= D.
 *
 * State: H vertices per side, A-side index a in 0..H-1, B-side index b in 0..H-1.
 * nbA[a*d+j] = B-index of a's j-th neighbour, nbB[b*d+j] = A-index.
 * Cost = number of unordered vertex pairs at distance > D (bitset ball expansion).
 * Moves: bipartite double-edge swaps (keep d-regularity and simplicity).
 * When cost hits 0 the graph is saved and grown by one vertex per side
 * (remove a matching of d edges, attach the new A vertex to their B ends and
 * the new B vertex to their A ends), then annealed again from that warm start.
 */

typedef uint64_t u64;

#define MAXD 16
#define MAXH 2048
#define PATIENCE 5000
#define MAXRE 8
#define T0 0.5
#define TMAX 2.5

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int d, D, H;
static int nbA[MAXH * MAXD], nbB[MAXH * MAXD];
static int bestA[MAXH * MAXD];
static u64 bufX[2 * MAXH * (2 * MAXH / 64)];
static u64 bufY[2 * MAXH * (2 * MAXH / 64)];

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static inline int nbr(int v, int j) {
    if (v < H) return H + nbA[v * d + j];
    return nbB[(v - H) * d + j];
}

/* Number of unordered pairs at distance > D (disconnected pairs included). */
static long long cost_eval(void) {
    int n = 2 * H, W = (n + 63) >> 6;
    memset(bufX, 0, sizeof(u64) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) bufX[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    u64 *cur = bufX, *nxt = bufY;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * W;
            u64 *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * (size_t)W);
            for (int j = 0; j < d; j++) {
                u64 *s2 = cur + (size_t)nbr(v, j) * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++)
            cnt += popc(cur[(size_t)v * W + w]);
    return ((long long)n * n - cnt) / 2;
}

/* Start: circulant bipartite d-regular graph on H + H vertices (needs H >= d). */
static void circulant_init(int h) {
    H = h;
    for (int a = 0; a < h; a++)
        for (int j = 0; j < d; j++)
            nbA[a * d + j] = (a + j) % h;
    for (int b = 0; b < h; b++)
        for (int j = 0; j < d; j++)
            nbB[b * d + j] = ((b - j) % h + h) % h;
}

/* Grow by one vertex per side, keeping d-regularity and simplicity. */
static int grow_ok(void) {
    static int order[MAXH], usedB[MAXH], pa[MAXD], pb[MAXD], pj[MAXD];
    for (int tries = 0; tries < 50; tries++) {
        for (int i = 0; i < H; i++) { order[i] = i; usedB[i] = 0; }
        for (int i = H - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = order[i]; order[i] = order[j]; order[j] = t;
        }
        int cnt = 0;
        for (int oi = 0; oi < H && cnt < d; oi++) {
            int a = order[oi];
            int j0 = rndi(d);
            for (int t = 0; t < d; t++) {
                int j = (j0 + t) % d;
                int b = nbA[a * d + j];
                if (!usedB[b]) {
                    usedB[b] = 1;
                    pa[cnt] = a; pb[cnt] = b; pj[cnt] = j;
                    cnt++;
                    break;
                }
            }
        }
        if (cnt == d) {
            int hn = H;
            for (int k = 0; k < d; k++) {
                int a = pa[k], b = pb[k], j = pj[k];
                nbA[a * d + j] = hn;               /* a now meets new B vertex hn */
                int p = 0;
                for (int q = 0; q < d; q++) if (nbB[b * d + q] == a) { p = q; break; }
                nbB[b * d + p] = hn;               /* b now meets new A vertex hn */
            }
            for (int k = 0; k < d; k++) {
                nbA[hn * d + k] = pb[k];           /* new A vertex adjacent to matched B ends */
                nbB[hn * d + k] = pa[k];           /* new B vertex adjacent to matched A ends */
            }
            H = hn + 1;
            return 1;
        }
    }
    return 0;
}

static int findpos_b(int b, int a) {
    for (int p = 0; p < d; p++) if (nbB[b * d + p] == a) return p;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int h0 = argc > 5 ? atoi(argv[5]) : 0;
    if (d < 3 || D < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (h0 < d) h0 = d;
    if (h0 > MAXH / 2) h0 = MAXH / 2;
    double tend = now() + tl;

    circulant_init(h0);
    long long cur = cost_eval();

    int bestH = 0;
    double T = T0;
    long long best_stage = cur;
    long long it = 0, last_imp = 0;
    int reheats = 0;

    while (now() < tend) {
        if (cur == 0) {
            bestH = H;
            memcpy(bestA, nbA, sizeof(int) * (size_t)H * (size_t)d);
            if (H + 1 >= MAXH) break;
            if (!grow_ok()) break;
            cur = cost_eval();
            best_stage = cur;
            last_imp = it;
            T = T0;
            reheats = 0;
            continue;
        }
        if (it - last_imp > PATIENCE) {
            if (++reheats > MAXRE) break;
            T *= 1.5;
            if (T > TMAX) T = TMAX;
            last_imp = it;
            continue;
        }

        it++;
        int a1 = rndi(H), a2 = rndi(H);
        if (a1 == a2) continue;
        int j1 = rndi(d), j2 = rndi(d);
        int b1 = nbA[a1 * d + j1], b2 = nbA[a2 * d + j2];
        if (b1 == b2) continue;
        int ok = 1;
        for (int t = 0; t < d; t++) {
            if (nbA[a1 * d + t] == b2 || nbA[a2 * d + t] == b1) { ok = 0; break; }
        }
        if (!ok) continue;

        int p1 = findpos_b(b1, a1), p2 = findpos_b(b2, a2);
        nbA[a1 * d + j1] = b2;
        nbA[a2 * d + j2] = b1;
        nbB[b1 * d + p1] = a2;
        nbB[b2 * d + p2] = a1;

        long long c2 = cost_eval();
        long long delta = c2 - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur < best_stage) { best_stage = cur; last_imp = it; }
        } else {
            nbA[a1 * d + j1] = b1;
            nbA[a2 * d + j2] = b2;
            nbB[b1 * d + p1] = a1;
            nbB[b2 * d + p2] = a2;
        }
    }

    if (bestH == 0) { printf("0 0\n"); return 0; }
    int n = 2 * bestH, m = bestH * d;
    printf("%d %d\n", n, m);
    for (int a = 0; a < bestH; a++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", a, bestH + bestA[a * d + j]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    if d < 3 or D < 3:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    # Warm-start size: a fraction of the Moore bound, kept modest so the
    # annealer starts from a graph it can repair quickly.
    h0 = max(d, min(400, lib.moore_bound(d, D) // 8))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), h0],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
