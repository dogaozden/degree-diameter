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

/* k-fixed tabu search at the current size K (minimise F). Returns 1 when F = 0 (S is a partial ovoid of size K).
   plate / plate_n: most recent state with F = 1, one endpoint of its conflicting pair dropped = valid (K-1)-set. */
static int tabu_run(int64_t IT, int TA, int TB, int32_t *plate, int *plate_n) {
    *plate_n = 0;
    for (int64_t it = 0; it < IT; it++) {
        iter++;
        if (F == 0) return 1;
        if (F == 1) {
            int32_t a = -1, b = -1;
            for (int i = 0; i < K; i++) { int w = S[i]; if (C[w]) { if (a < 0) a = w; else b = w; } }
            int32_t drop = rndn(2) ? a : b;
            int n = 0; for (int i = 0; i < K; i++) if (S[i] != drop) plate[n++] = S[i];
            *plate_n = n;
        }
        /* u: conflicting member of S with most conflicts, not tabu */
        int bu = -1, bc = -1, nc = 0;
        for (int i = 0; i < K; i++) {
            int w = S[i]; int cw = C[w];
            if (cw == 0 || TOUT[w] > iter) continue;
            if (cw > bc) { bc = cw; bu = w; nc = 1; }
            else if (cw == bc) { nc++; if (rndn((uint32_t)nc) == 0) bu = w; }
        }
        if (bu < 0) {
            int nn = 0;
            for (int i = 0; i < K; i++) { int w = S[i]; if (C[w]) { nn++; if (rndn((uint32_t)nn) == 0) bu = w; } }
        }
        int u = bu;
        /* v: outside, not tabu, minimising conflicts after removing u */
        stamp++;
        const uint16_t *nbu = NB + (size_t)u * DEG;
        for (int t = 0; t < DEG; t++) MARK[nbu[t]] = stamp;
        int best = 1 << 30, ncand = 0;
        for (int w = 0; w < NP; w++) {
            if (INS[w] || TIN[w] > iter) continue;
            int sc = (int)C[w] - (MARK[w] == stamp ? 1 : 0);
            if (sc < best) { best = sc; ncand = 0; }
            if (sc == best) CAND[ncand++] = w;
        }
        int v;
        if (ncand == 0) { do { v = (int)rndn(NP); } while (INS[v]); }
        else v = CAND[rndn((uint32_t)ncand)];
        rem_v(u);
        add_v(v);
        TIN[u] = iter + TA + (int64_t)rndn((uint32_t)TB);
        TOUT[v] = iter + 1 + (int64_t)rndn(3);
    }
    return F == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ils HEXBIN START SEED SECONDS OUTPREFIX [IT RMAX]\n"); return 2; }
    build_field();
    load(argv[1]);
    const char *startf = argv[2];
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double secs = atof(argv[4]);
    const char *outp = argv[5];
    int64_t IT = argc > 6 ? atoll(argv[6]) : 20000;
    int RMAX = argc > 7 ? atoi(argv[7]) : 10;
    if (RMAX < 2) RMAX = 2;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    double t0 = now();
    build_nb();
    fprintf(stderr, "neighbour lists built in %.1f s\n", now() - t0);
    for (int i = 0; i < NP; i++) POS[i] = -1;

    static int32_t base[MAXK + 2], plate[MAXK + 2];
    int K0 = read_set(startf, base);
    if (!is_valid(base, K0)) { fprintf(stderr, "start set is not a partial ovoid\n"); return 3; }
    fprintf(stderr, "start size %d (valid)\n", K0);
    {
        for (int i = 0; i < K0; i++) add_v(base[i]);
        int hist[12] = {0}; int minc = 1 << 30;
        for (int w = 0; w < NP; w++) if (!INS[w]) { if (C[w] < 12) hist[C[w]]++; if ((int)C[w] < minc) minc = C[w]; }
        fprintf(stderr, "outside points: min C = %d; counts for C = 0..11:", minc);
        for (int c = 0; c < 12; c++) fprintf(stderr, " %d", hist[c]);
        fprintf(stderr, "\n");
        clear_all();
    }

    int64_t outer = 0, plateau_moves = 0, records = 0;
    double last_print = now();
    char fn[4200];
    while (now() - t0 < secs) {
        outer++;
        clear_all();
        for (int i = 0; i < K0; i++) add_v(base[i]);
        if (rndn(2) == 0) {  /* random removal of r members */
            int r = 2 + (int)rndn((uint32_t)(RMAX - 1));
            for (int p = 0; p < r && K > 0; p++) rem_v(S[rndn((uint32_t)K)]);
        } else {             /* forced insertion of a low-conflict outside point (ARW style) */
            int w0 = -1;
            for (int tries = 0; tries < 10000000 && w0 < 0; tries++) {
                int w = (int)rndn(NP);
                if (!INS[w] && C[w] <= FORCEC) w0 = w;
            }
            int32_t drop[64]; int nd = 0;
            for (int i = 0; i < K; i++) if (Bxy(X + 7 * w0, X + 7 * S[i]) == 0) drop[nd++] = S[i];
            for (int i = 0; i < nd; i++) rem_v(drop[i]);
            add_v(w0);
            int extra = (int)rndn(3);
            for (int p = 0; p < extra && K > 0; p++) rem_v(S[rndn((uint32_t)K)]);
        }
        /* refill with conflict-free points while there are any */
        for (;;) {
            int nf = 0, pick = -1;
            for (int w = 0; w < NP; w++) if (!INS[w] && C[w] == 0) { nf++; if (rndn((uint32_t)nf) == 0) pick = w; }
            if (pick < 0) break;
            add_v(pick);
        }
        /* fill to K0+1 with minimum-conflict points */
        while (K < K0 + 1) {
            int best = 1 << 30, nc = 0;
            for (int w = 0; w < NP; w++) if (!INS[w]) {
                int c = C[w];
                if (c < best) { best = c; nc = 0; }
                if (c == best) CAND[nc++] = w;
            }
            add_v(CAND[rndn((uint32_t)nc)]);
        }
        int plate_n = 0;
        int ok = tabu_run(IT, 7, 10, plate, &plate_n);
        if (ok) {
            if (!is_valid(S, K)) { fprintf(stderr, "BUG: invalid record\n"); return 4; }
            K0 = K;
            memcpy(base, S, sizeof(int32_t) * K0);
            records++;
            snprintf(fn, sizeof fn, "%s_%d.txt", outp, K0);
            write_set(fn, base, K0);
            fprintf(stderr, "[c1] NEW SIZE %d at t=%.1fs outer=%lld iter=%lld -> %s\n", K0, now() - t0,
                    (long long)outer, (long long)iter, fn);
        } else if (plate_n == K0 && is_valid(plate, K0)) {
            memcpy(base, plate, sizeof(int32_t) * K0);
            plateau_moves++;
        }
        if (now() - last_print > 10.0) {
            last_print = now();
            fprintf(stderr, "[c1] t=%.0fs outer=%lld iter=%lld (%.0f/s) base=%d records=%lld plateau=%lld\n",
                    now() - t0, (long long)outer, (long long)iter, iter / (now() - t0), K0,
                    (long long)records, (long long)plateau_moves);
        }
    }
    fprintf(stderr, "[c1] done: final base size %d, records %lld, plateau moves %lld, outer %lld, iter %lld, %.1fs\n",
            K0, (long long)records, (long long)plateau_moves, (long long)outer, (long long)iter, now() - t0);
    printf("%d\n", K0);
    return 0;
}
