/* ils.c  (card c1, squad round 5, d10D7)
   Iterated local search from a partial ovoid of H(8): a set of pairwise opposite points of Q(6,8),
   x and y opposite iff B(x,y) != 0 (B = symplectic form of the README; the nucleus projection is implicit).

   Loop (base = a valid K0-set, initially best134.txt):
     - remove r random members (r = 2..RMAX), refill with conflict-free points, fill to K0+1 with min-conflict points;
     - k-fixed tabu search at size K0+1, minimising F = number of conflicting pairs, for IT iterations;
     - F = 0 -> a valid (K0+1)-set: verified, written to OUTPREFIX_<size>.txt, becomes the base;
     - otherwise the most recent F = 1 state with one endpoint of its conflicting pair dropped is a valid K0-set:
       it becomes the new base (equal-size move, plateau walk).

   build: gcc -O2 -o ils ils.c
   run:   ./ils HEXBIN START SEED SECONDS OUTPREFIX [IT RMAX]
   Neighbour lists: uint16, N*4680*2 bytes = 351 MB.
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define NP 37449
#define DEG 4680
#define QP 9
#define MAXK 1024
#define FORCEC 4   /* forced insertions use outside points with at most FORCEC conflicts (min is 3 at best134) */

static uint8_t MULT[8][8];
static uint8_t X[NP * 7];
static uint16_t *NB;
static uint16_t C[NP];
static uint8_t INS[NP];
static int32_t POS[NP];
static int32_t S[MAXK + 2];
static int K, F;
static int64_t TIN[NP], TOUT[NP];
static uint32_t MARK[NP], stamp = 0;
static int32_t CAND[NP];
static int64_t iter = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline uint32_t rndn(uint32_t n) { return (uint32_t)(rnd() % n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

/* GF(8) = GF(2)[x]/(x^3+x+1), element a0 + 2 a1 + 4 a2 (same as research/d10D7/hexgen2.c and pov.c) */
static void build_field(void) {
    for (int x = 0; x < 8; x++) for (int y = 0; y < 8; y++) {
        int a[3] = {x & 1, (x >> 1) & 1, (x >> 2) & 1};
        int b[3] = {y & 1, (y >> 1) & 1, (y >> 2) & 1};
        int r[5] = {0, 0, 0, 0, 0};
        for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) r[i + j] ^= a[i] & b[j];
        for (int k = 4; k >= 3; k--) if (r[k]) { r[k] = 0; r[k - 3] ^= 1; r[k - 2] ^= 1; }
        MULT[x][y] = (uint8_t)(r[0] | (r[1] << 1) | (r[2] << 2));
    }
}

static inline int Bxy(const uint8_t *x, const uint8_t *y) {
    return MULT[x[0]][y[4]] ^ MULT[x[4]][y[0]] ^ MULT[x[1]][y[5]] ^ MULT[x[5]][y[1]] ^ MULT[x[2]][y[6]] ^ MULT[x[6]][y[2]];
}

static void load(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(2); }
    int32_t h[3];
    if (fread(h, 4, 3, f) != 3 || h[0] != 8 || h[1] != NP) { fprintf(stderr, "bad header\n"); exit(2); }
    if (fseek(f, (long)NP * QP * 4, SEEK_CUR) != 0) { fprintf(stderr, "seek failed\n"); exit(2); }
    if (fread(X, 1, NP * 7, f) != NP * 7) { fprintf(stderr, "short coordinates\n"); exit(2); }
    fclose(f);
}

static void build_nb(void) {
    NB = malloc((size_t)NP * DEG * sizeof(uint16_t));
    if (!NB) { fprintf(stderr, "malloc failed\n"); exit(2); }
    static uint16_t cnt[NP];
    for (int i = 0; i < NP; i++) {
        const uint8_t *x = X + 7 * i;
        for (int j = i + 1; j < NP; j++) {
            if (Bxy(x, X + 7 * j) == 0) {
                if (cnt[i] >= DEG || cnt[j] >= DEG) { fprintf(stderr, "degree overflow\n"); exit(3); }
                NB[(size_t)i * DEG + cnt[i]++] = (uint16_t)j;
                NB[(size_t)j * DEG + cnt[j]++] = (uint16_t)i;
            }
        }
    }
    for (int i = 0; i < NP; i++) if (cnt[i] != DEG) { fprintf(stderr, "vertex %d degree %d\n", i, cnt[i]); exit(3); }
}

/* C[w] = number of members of S conflicting with w (B(w,s) = 0); F = number of conflicting pairs inside S */
static void add_v(int v) {
    INS[v] = 1; POS[v] = K; S[K++] = v; F += C[v];
    const uint16_t *nb = NB + (size_t)v * DEG;
    for (int t = 0; t < DEG; t++) C[nb[t]]++;
}
static void rem_v(int u) {
    int p = POS[u]; int32_t last = S[--K]; S[p] = last; POS[last] = p; POS[u] = -1; INS[u] = 0;
    F -= C[u];
    const uint16_t *nb = NB + (size_t)u * DEG;
    for (int t = 0; t < DEG; t++) C[nb[t]]--;
}
static void clear_all(void) { while (K) rem_v(S[K - 1]); }

static int is_valid(const int32_t *a, int n) {
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++)
        if (a[i] == a[j] || Bxy(X + 7 * a[i], X + 7 * a[j]) == 0) return 0;
    return 1;
}

static int read_set(const char *fn, int32_t *a) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    int n = 0, x;
    while (fscanf(f, "%d", &x) == 1) {
        if (x < 0 || x >= NP || n >= MAXK) { fprintf(stderr, "bad id %d\n", x); exit(2); }
        a[n++] = x;
    }
    fclose(f); return n;
}

static void write_set(const char *fn, const int32_t *a, int n) {
    char tmp[4200]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *f = fopen(tmp, "w"); if (!f) { perror(tmp); exit(2); }
    for (int i = 0; i < n; i++) fprintf(f, "%d\n", a[i]);
    fclose(f); rename(tmp, fn);
}

/* ---- closure LNS (card c1): remove R (a subset of the members of S) and solve the maximum independent set
   exactly on candidates = R + {outside w : every S-neighbour of w lies in R}. Size > |R| is a gain (valid set). */
static int32_t cntR[NP];      /* number of R members adjacent to w */
static uint8_t inR[NP];       /* membership of S members in R */
static uint64_t ADJ[64];
static uint64_t bestmask;
static int bestsz;

static void add_R(int s) {
    const uint16_t *nb = NB + (size_t)s * DEG;
    for (int t = 0; t < DEG; t++) cntR[nb[t]]++;
}

static void bb(uint64_t cand, uint64_t cur, int sz) {
    if (sz + __builtin_popcountll(cand) <= bestsz) return;
    if (!cand) { bestsz = sz; bestmask = cur; return; }
    int v = __builtin_ctzll(cand);
    bb(cand & ~ADJ[v] & ~(1ULL << v), cur | (1ULL << v), sz + 1);
    bb(cand & ~(1ULL << v), cur, sz);
}

static int score_now(void) {  /* closeness of the outside points to being free: sum of max(0, 4 - C) */
    int s = 0;
    for (int w = 0; w < NP; w++) if (!INS[w] && C[w] < 4) s += 4 - C[w];
    return s;
}
#define PLATEAU_WORSE_PCT 5

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns HEXBIN START SEED SECONDS OUTPREFIX [RMAX]\n"); return 2; }
    build_field();
    load(argv[1]);
    const char *startf = argv[2];
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double secs = atof(argv[4]);
    const char *outp = argv[5];
    int RMAX = argc > 6 ? atoi(argv[6]) : 20;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double t0 = now();
    build_nb();
    fprintf(stderr, "neighbour lists built in %.1f s\n", now() - t0);
    for (int i = 0; i < NP; i++) POS[i] = -1;
    static int32_t base[MAXK + 2], Rl[MAXK + 2], ids[64], newI[64];
    static uint8_t isR[64];
    int K0 = read_set(startf, base);
    if (!is_valid(base, K0)) { fprintf(stderr, "start set is not a partial ovoid\n"); return 3; }
    for (int i = 0; i < K0; i++) add_v(base[i]);
    fprintf(stderr, "start size %d (valid), RMAX %d\n", K0, RMAX);
    int64_t iters = 0, improve = 0, plateau = 0, skipped = 0, closure_sum = 0, trivial = 0;
    double last_print = now();
    char fn[4200];
    while (now() - t0 < secs) {
        iters++;
        int p = -1;
        for (int tries = 0; tries < 10000000 && p < 0; tries++) {
            int w = (int)rndn(NP);
            if (!INS[w] && C[w] >= 1 && C[w] <= 5) p = w;
        }
        memset(cntR, 0, sizeof cntR);
        memset(inR, 0, sizeof inR);
        int nR = 0;
        for (int i = 0; i < K; i++) {
            int s = S[i];
            if (Bxy(X + 7 * p, X + 7 * s) == 0) { Rl[nR++] = s; inR[s] = 1; add_R(s); }
        }
        /* grow R: repeatedly close the outside point with fewest missing S-neighbours (random ties) */
        while (nR < RMAX) {
            int bm = 1 << 30, nc = 0;
            for (int w = 0; w < NP; w++) {
                if (INS[w] || cntR[w] == 0) continue;
                int miss = (int)C[w] - (int)cntR[w];
                if (miss <= 0) continue;
                if (miss < bm) { bm = miss; nc = 0; }
                if (miss == bm) CAND[nc++] = w;
            }
            if (nc == 0) break;
            int w = CAND[rndn((uint32_t)nc)];
            for (int i = 0; i < K; i++) {
                int s = S[i];
                if (!inR[s] && Bxy(X + 7 * w, X + 7 * s) == 0) { Rl[nR++] = s; inR[s] = 1; add_R(s); }
            }
        }
        /* closure: R members, and outside points whose S-neighbours all lie in R (free points included) */
        int m = 0;
        for (int i = 0; i < nR; i++) { ids[m] = Rl[i]; isR[m] = 1; m++; }
        int nout = 0, overflow = 0;
        for (int w = 0; w < NP; w++) {
            if (INS[w] || cntR[w] != C[w]) continue;
            if (m >= 62) { overflow = 1; break; }
            ids[m] = w; isR[m] = 0; m++; nout++;
        }
        if (overflow) { skipped++; continue; }
        closure_sum += nout; if (nout == 0) trivial++;
        /* shuffle candidates (random tie-breaking in the exact search) */
        for (int i = m - 1; i > 0; i--) {
            int j = (int)rndn((uint32_t)(i + 1));
            int32_t ti = ids[i]; ids[i] = ids[j]; ids[j] = ti;
            uint8_t tr = isR[i]; isR[i] = isR[j]; isR[j] = tr;
        }
        uint64_t Rmask = 0;
        for (int i = 0; i < m; i++) { ADJ[i] = 0; if (isR[i]) Rmask |= 1ULL << i; }
        for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++)
            if (Bxy(X + 7 * ids[i], X + 7 * ids[j]) == 0) { ADJ[i] |= 1ULL << j; ADJ[j] |= 1ULL << i; }
        uint64_t all = (m >= 64) ? ~0ULL : ((1ULL << m) - 1);
        bestsz = nR - 1; bestmask = 0;
        bb(all, 0, 0);
        if (bestsz > nR || (bestsz == nR && bestmask != Rmask)) {
            int ni = 0;
            for (int i = 0; i < m; i++) if ((bestmask >> i) & 1ULL) newI[ni++] = ids[i];
            int sc_old = score_now();
            for (int i = 0; i < nR; i++) rem_v(Rl[i]);
            for (int i = 0; i < ni; i++) add_v(newI[i]);
            if (F != 0 || !is_valid(S, K)) { fprintf(stderr, "BUG: invalid move (F=%d)\n", F); return 4; }
            int sc_new = score_now();
            int accept = (bestsz > nR) || (sc_new >= sc_old) || ((int)rndn(100) < PLATEAU_WORSE_PCT);
            if (!accept) {
                for (int i = 0; i < ni; i++) rem_v(newI[i]);
                for (int i = 0; i < nR; i++) add_v(Rl[i]);
                if (F != 0) { fprintf(stderr, "BUG: revert F=%d\n", F); return 4; }
            } else if (bestsz > nR) {
                improve++;
                snprintf(fn, sizeof fn, "%s_%d.txt", outp, K);
                write_set(fn, S, K);
                fprintf(stderr, "[c1-lns2] NEW SIZE %d at t=%.1fs iter=%lld (|R|=%d, closure %d) -> %s\n", K, now() - t0,
                        (long long)iters, nR, nout, fn);
            } else plateau++;
        }
        if (now() - last_print > 10.0) {
            last_print = now();
            fprintf(stderr, "[c1-lns2] t=%.0fs iters=%lld K=%d improve=%lld plateau=%lld skipped=%lld avg_closure=%.2f trivial=%lld\n",
                    now() - t0, (long long)iters, K, (long long)improve, (long long)plateau, (long long)skipped,
                    (double)closure_sum / (iters - skipped), (long long)trivial);
        }
    }
    fprintf(stderr, "[c1-lns2] done: K=%d improve=%lld plateau=%lld iters=%lld avg_closure=%.2f trivial=%lld time=%.1fs\n",
            K, (long long)improve, (long long)plateau, (long long)iters,
            (double)closure_sum / (iters - skipped > 0 ? iters - skipped : 1), (long long)trivial, now() - t0);
    printf("%d\n", K);
    return 0;
}
