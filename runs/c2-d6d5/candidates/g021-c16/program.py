import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 8
#define MAXK 6
#define GMAX 1500
#define CAND 24

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Lift model: base has k A-blocks and k B-blocks, d layers. In layer l, A-block i
   is matched to B-block tgt[l][i] (a permutation per layer) with voltage vol[l][i].
   Dart (l,i): A_{i,g} ~ B_{j, g*s} for all g in the group. */
static int d_, D_, k_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int tgt[MAXD][MAXK], vol[MAXD][MAXK];
static int btgt[MAXD][MAXK], bvol[MAXD][MAXK];
static int tabu_until[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;
static u64 full_mask = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    G_ = G;
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

static void set_dart(int l, int i) {
    int G = G_, k = k_, N = N_, j = tgt[l][i], s = vol[l][i];
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int h = MT[g * G + s];
        row[i * G + g] = (k + j) * G + h;
        row[(k + j) * G + h] = i * G + RS[s * G + h];
    }
}

static void save_best_state(void) {
    memcpy(btgt, tgt, sizeof tgt);
    memcpy(bvol, vol, sizeof vol);
}

static void restore_best_state(void) {
    memcpy(tgt, btgt, sizeof tgt);
    memcpy(vol, bvol, sizeof vol);
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) set_dart(l, i);
}

/* Cost = unreached (source-block, vertex) pairs + heavy penalty for duplicate darts. */
static long long evalcost(void) {
    int N = N_, G = G_, k = k_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[(size_t)l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (tgt[l][i] == tgt[l2][i] && vol[l][i] == vol[l2][i]) dup++;
    return unreached + 1000 * dup;
}

static void random_init(void) {
    int d = d_, k = k_, G = G_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { tgt[l][i] = perm[i]; vol[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
    memset(tabu_until, 0, sizeof tabu_until);
}

typedef struct { int type, l, i1, i2, ov, nv; } Move;

static void mv_apply(const Move *m) {
    if (m->type == 0) {
        vol[m->l][m->i1] = m->nv;
        set_dart(m->l, m->i1);
    } else {
        int t = tgt[m->l][m->i1];
        tgt[m->l][m->i1] = tgt[m->l][m->i2];
        tgt[m->l][m->i2] = t;
        set_dart(m->l, m->i1);
        set_dart(m->l, m->i2);
    }
}

static void mv_undo(const Move *m) {
    if (m->type == 0) {
        vol[m->l][m->i1] = m->ov;
        set_dart(m->l, m->i1);
    } else {
        mv_apply(m); /* a swap is its own inverse */
    }
}

/* Uses rch of the CURRENT state (must be refreshed before calling). */
static Move gen_move(void) {
    Move m;
    int d = d_, k = k_, G = G_, N = N_;
    m.ov = 0; m.nv = 0;
    if (k >= 2 && rndu() < 0.2) {
        m.type = 1;
        m.l = rndi(d);
        m.i1 = rndi(k);
        m.i2 = rndi(k - 1);
        if (m.i2 >= m.i1) m.i2++;
        return m;
    }
    m.type = 0;
    m.i2 = 0;
    int l = rndi(d), i = rndi(k);
    if (rndu() < 0.6) {
        int start = rndi(N), v = -1;
        for (int q = 0; q < N; q++) {
            int w = (start + q) % N;
            if (rch[w] != full_mask) { v = w; break; }
        }
        if (v >= 0) {
            int b = v / G;
            if (b < k) {
                i = b;
            } else {
                int jb = b - k, found = -1;
                for (int ii = 0; ii < k; ii++)
                    if (tgt[l][ii] == jb) { found = ii; break; }
                if (found >= 0) i = found;
            }
        }
    }
    m.l = l;
    m.i1 = i;
    m.ov = vol[l][i];
    int nw = rndi(G);
    if (nw == m.ov) nw = (nw + 1) % G;
    m.nv = nw;
    return m;
}

static int is_tabu(const Move *m, int it) {
    if (tabu_until[m->l][m->i1] > it) return 1;
    if (m->type == 1 && tabu_until[m->l][m->i2] > it) return 1;
    return 0;
}

static void set_tabu(const Move *m, int it) {
    int ten = 4 + rndi(8);
    tabu_until[m->l][m->i1] = it + ten;
    if (m->type == 1) tabu_until[m->l][m->i2] = it + ten;
}

/* Tabu search over darts: each step evaluates a random candidate set (defect-biased),
   takes the best admissible move even if worse, restarts from best after stagnation. */
static long long tabu_run(int maxit, int maxkick, int stag_lim, double deadline, int *found) {
    int k = k_, d = d_, G = G_;
    random_init();
    long long cur = evalcost();
    long long best = cur;
    save_best_state();
    int stagn = 0, kicks = 0;
    for (int it = 1; it <= maxit && cur > 0; it++) {
        if ((it & 7) == 0 && now() > deadline) break;
        Move cand[CAND];
        long long cv[CAND];
        for (int c = 0; c < CAND; c++) cand[c] = gen_move();
        for (int c = 0; c < CAND; c++) {
            mv_apply(&cand[c]);
            cv[c] = evalcost();
            mv_undo(&cand[c]);
        }
        int bi = -1;
        long long bc = 0;
        for (int c = 0; c < CAND; c++) {
            if (is_tabu(&cand[c], it) && cv[c] >= best) continue;
            if (bi < 0 || cv[c] < bc || (cv[c] == bc && rndi(2))) { bi = c; bc = cv[c]; }
        }
        if (bi < 0) { cur = evalcost(); continue; }
        mv_apply(&cand[bi]);
        set_tabu(&cand[bi], it);
        cur = evalcost();
        if (cur < best) {
            best = cur;
            save_best_state();
            stagn = 0;
        } else {
            stagn++;
        }
        if (stagn > stag_lim) {
            if (kicks >= maxkick) break;
            kicks++;
            restore_best_state();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                vol[l][i] = rndi(G);
                set_dart(l, i);
            }
            cur = evalcost();
            stagn = 0;
        }
    }
    restore_best_state();
    *found = (best == 0);
    return best;
}

static void emit_best(void) {
    int kG = k_ * G_, d = d_, N = N_;
    int cnt = kG * d;
    int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
    int p = 0;
    for (int u = 0; u < kG; u++)
        for (int l = 0; l < d; l++) {
            ne[2 * p] = u;
            ne[2 * p + 1] = nb[(size_t)l * N + u];
            p++;
        }
    free(bE);
    bE = ne;
    bEc = cnt;
    bestN = N;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    if (minN < 2) minN = 2;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    double trial_len = tl / 10.0;
    if (trial_len < 1.5) trial_len = 1.5;
    static const int Ks[10] = {1, 1, 2, 2, 2, 3, 3, 4, 5, 6};
    static const int K2s[8] = {1, 1, 1, 2, 2, 3, 4, 6};
    static int cand[GMAX + 5];

    int target = minN;
    int fails = 0;
    while (now() < tend) {
        int k = Ks[rndi(10)];
        int Gmin = (target + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 25 + 2);
        int k2 = K2s[rndi(8)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        k_ = k;
        full_mask = (1ULL << (2 * k)) - 1;
        alloc_state(2 * k * G_);

        double cap = now() + trial_len;
        double dl = cap < tend ? cap : tend;
        int found = 0;
        tabu_run(4000, 3, 250, dl, &found);
        if (found && N_ > bestN) {
            emit_best();
            fails = 0;
            target = N_ + 1 + N_ / 40;
        } else if (found) {
            fails = 0;
        } else {
            fails++;
            if (fails >= 3) {
                fails = 0;
                target = bestN > 0 ? bestN + 1 : minN;
            }
        }
        if (target <= bestN) target = bestN + 1;
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    if d < 3 or D < 3:
        return best

    # Use almost the whole limit; the C engine stops itself at `budget`.
    budget = max(0.5, time_limit - 6.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
