"""Multi-orbit lifts over two group families for the bipartite degree-diameter problem.

Change in this version: the C engine searches two different groups.
  * type 0: affine groups F_q x| H (as before), |G| = q*c with c | q-1.
  * type 1: semidirect products Z_m x|_r Z_k with r^k = 1 mod m and gcd(r, m) = 1
    (r = 1 gives the abelian Z_m x Z_k). These are not affine, so they cover
    base groups the affine family never reaches.

Each dart slot t of orbit i is a voltage v; left orbit i sends its t-th dart to right
orbit tgt[i][t]. Left translations by G are automorphisms transitive on each orbit,
so BFS from the 2B orbit representatives decides the diameter. Phases: B = 1 first
(2N vertices, reached by the previous family at 2510), then B = 3 (6N), then B = 2,
then extend whichever family is best. The C engine checks simplicity and, when the
graph is small enough, a full BFS before printing. Python checks the result with
lib.is_valid and keeps a valid fallback.
"""
import time

import lib

C_SOURCE = r'''
/* Multi-orbit lifts over G (affine F_q x| H, or Z_m x|_r Z_k), B in {1,2,3} orbits.
 * Usage: prog d D seed time_limit lo3 hi3 lo1 hi1 lo2 hi2
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4800
#define MAXD 32
#define MAXB 3
#define MAXCAND 60000

typedef struct { int type, x1, x2, x3, x4, N; } Cand;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;
    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group state */

static int GTYPE = 1, GN, GC, GM, GK;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int PWR[MAXN];

static void setup_group(const Cand *cd) {
    GTYPE = cd->type;
    GN = cd->N;
    if (GTYPE == 0) {
        int q = cd->x1, p = cd->x2, k = cd->x3, c = cd->x4;
        build_field(q, p, k);
        GC = c;
        int g = -1;
        for (int g0 = 2; g0 < q && g < 0; g0++) {
            int x = 1, ord = 0;
            do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
            if (ord == q - 1) g = g0;
        }
        PWG[0] = 1;
        for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
        int step = (q - 1) / c;
        for (int j = 0; j < q; j++) hidx[j] = -1;
        for (int t = 0; t < c; t++) {
            Hel[t] = PWG[(t * step) % (q - 1)];
            hidx[Hel[t]] = t;
        }
        for (int j = 0; j < c; j++)
            for (int t = 0; t < c; t++)
                HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
    } else {
        GM = cd->x1;
        GK = cd->x2;
        PWR[0] = 1 % GM;
        for (int b = 1; b < GK; b++) PWR[b] = (int)((long)PWR[b - 1] * cd->x3 % GM);
    }
}

/* Semidirect: (a,b)(c,e) = (a + r^b c, b + e), element coded a*GK + b. */
static inline int gmul(int x, int y) {
    if (GTYPE == 1) {
        int a = x / GK, b = x - a * GK, c2 = y / GK, e = y - c2 * GK;
        int na = (a + (int)((long)PWR[b] * c2 % GM)) % GM;
        int nb = b + e;
        if (nb >= GK) nb -= GK;
        return na * GK + nb;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    if (GTYPE == 1) {
        int a = x / GK, b = x - a * GK;
        int nb = (GK - b) % GK;
        int na = (GM - (int)((long)PWR[nb] * a % GM)) % GM;
        return na * GK + nb;
    }
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ multi-orbit lift */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB;
static Cand bestCand;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static int base_connected(int B) {
    int seenL[MAXB], seenR[MAXB];
    for (int i = 0; i < B; i++) { seenL[i] = 0; seenR[i] = 0; }
    seenL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int j = tgt[i][t];
                if (seenL[i] && !seenR[j]) { seenR[j] = 1; changed = 1; }
                if (seenR[j] && !seenL[i]) { seenL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!seenL[i] || !seenR[i]) return 0;
    return 1;
}

static int set_incidence(int B) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= d) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != d) return 0;
    return 1;
}

static void random_pattern(int B) {
    for (;;) {
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (base_connected(B) && set_incidence(B)) break;
    }
    curB = B;
}

static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* BFS up to depth D from src; returns number of vertices reached. */
static int bfs_count(int src) {
    int N = GN, BN = curB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over voltages; restarts draw a fresh random base pattern. */
static int search_group(double until) {
    int N = GN, B = curB;
    const int iters = 20000;
    while (now() < until) {
        random_pattern(B);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0 && simple_state(B)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static Cand cand[MAXCAND];
static int nc = 0;

static int cmpc(const void *x, const void *y) {
    const Cand *a = (const Cand *)x, *b = (const Cand *)y;
    if (a->N != b->N) return a->N - b->N;
    return a->type - b->type;
}

static void add_cand(int type, int x1, int x2, int x3, int x4, int N) {
    if (nc < MAXCAND) {
        Cand c = {type, x1, x2, x3, x4, N};
        cand[nc++] = c;
    }
}

static void build_cands(int lo, int hi) {
    nc = 0;
    /* Affine groups F_q x| H. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            add_cand(0, q, p, k, c, (int)N);
        }
    }
    /* Semidirect Z_m x|_r Z_k with r^k = 1 mod m. */
    for (int m = 3; (long)m * 2 <= hi; m++) {
        int kmin = (lo + m - 1) / m;
        if (kmin < 2) kmin = 2;
        for (int k = kmin; (long)m * k <= hi; k++) {
            int N = m * k;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                long x = 1 % m;
                for (int i = 0; i < k; i++) x = x * r % m;
                if (x == 1 % m) add_cand(1, m, k, r, 0, N);
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);
}

static void record(int B, const Cand *cd) {
    int total = 2 * B * cd->N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestCand = *cd;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Binary search over the sorted candidates for a feasible group, then extend upward. */
static void search_phase(int B, int lo, int hi, double until) {
    build_cands(lo, hi);
    if (nc == 0) return;
    int bestIdx = -1, bestNp = 0;
    int a = 0, b = nc - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = rem * 0.2;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        setup_group(&cand[mid]);
        curB = B;
        if (search_group(now() + slice)) {
            record(B, &cand[mid]);
            if (cand[mid].N > bestNp) { bestNp = cand[mid].N; bestIdx = mid; }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bestIdx < 0) return;
    int fails = 0, idx = bestIdx + 1;
    while (idx < nc && now() < until && fails < 2) {
        if (cand[idx].N <= bestNp) { idx++; continue; }
        double rem = until - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(&cand[idx]);
        curB = B;
        if (search_group(now() + slice)) {
            record(B, &cand[idx]);
            bestNp = cand[idx].N;
            bestIdx = idx;
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo3 = atoi(argv[5]), hi3 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    int lo2 = atoi(argv[9]), hi2 = atoi(argv[10]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi3 > MAXN - 1) hi3 = MAXN - 1;
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (hi2 > MAXN - 1) hi2 = MAXN - 1;
    if (lo3 < 2 * d) lo3 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;
    if (lo2 < 2 * d) lo2 = 2 * d;

    double span = t_end - t0;

    /* Phase 1: two orbits per side (total 2N); the family that gave the strongest result before. */
    if (lo1 <= hi1) search_phase(1, lo1, hi1, t0 + 0.35 * span);
    /* Phase 2: three orbits per side (total 6N). */
    if (lo3 <= hi3) search_phase(3, lo3, hi3, t0 + 0.7 * span);
    /* Phase 3: two orbits per side with the B = 2 pattern (total 4N). */
    if (lo2 <= hi2) search_phase(2, lo2, hi2, t0 + 0.85 * span);

    /* Extend the best family upward. */
    if (bestTotal > 0) {
        int eb = bestB;
        int ehi = (eb == 1) ? hi1 : (eb == 2 ? hi2 : hi3);
        if (bestCand.N + 1 <= ehi) search_phase(eb, bestCand.N + 1, ehi, t_end);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    int B = bestB;
    setup_group(&bestCand);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) { printf("0 0\n"); return 0; }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[2 * MAXB * MAXN][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Simplicity: no repeated neighbour anywhere. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adj[v][k] == adj[v][l]) { printf("0 0\n"); return 0; }

    /* Full check from every vertex when affordable; Python re-checks anyway. */
    if (V <= 6000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) { printf("0 0\n"); return 0; }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adj[v][t]);
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
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Leave room for the one-time C compile and the Python checks.
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
        lo3 = max(2 * d, best[0] // 6 + 1, mb // 24)
        hi3 = mb // 6
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        lo2 = max(2 * d, mb // 16)
        hi2 = mb // 4
        if budget > 4.0 and (lo3 <= hi3 or lo1 <= hi1 or lo2 <= hi2):
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, int(seed), round(budget, 2),
                                  int(lo3), int(hi3), int(lo1), int(hi1),
                                  int(lo2), int(hi2)],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
