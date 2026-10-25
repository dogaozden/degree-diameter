/* pov.c  (card c1, squad round 4, d10D7)
   Largest set of pairwise opposite points of H(8).
   Points = points of Q(6,8); x, y opposite iff B(x,y) != 0 (research/squads/d10D7-r4/README.md).
   Conflict graph: x ~ y iff B(x,y) = 0 and x != y (degree 4680). A partial ovoid = independent set.

   Method: k-fixed swap-based tabu search (min-conflicts). S has size K, F = number of conflicting pairs in S.
   Move = swap u in S (max conflicts, non-tabu) with v outside (min conflicts after removing u, non-tabu).
   Whenever F = 0 the set is a partial ovoid: it is saved and K grows by one.
   Neighbour lists are stored as uint16 (N*4680*2 bytes = 351 MB).

   build: gcc -O2 -o pov pov.c
   test:  ./pov HEXBIN test
   run:   ./pov HEXBIN SEED SECONDS OUTFILE [TA TB STALL PERT RESTART ADDFREE]
          OUTFILE is rewritten (one point id per line) every time the size grows.
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define NP 37449
#define DEG 4680
#define QP 9

static uint8_t MULT[8][8];
static uint8_t X[NP * 7];
static int32_t LPT[NP * QP];
static int32_t PLT[NP * QP];
static uint16_t *NB;
static uint16_t C[NP];
static uint8_t INS[NP];
static int32_t POS[NP];
static int32_t S[NP];
static int K, F;
static int64_t lastGrow = 0, epochMaxIter = 0;
static int epochMax = 0, epochNo = 0;
static int32_t TIN[NP], TOUT[NP];
static uint32_t MARK[NP], stamp = 0;
static int32_t CAND[NP];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline uint32_t rndn(uint32_t n) { return (uint32_t)(rnd() % n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

/* GF(8) = GF(2)[x]/(x^3+x+1), element a0 + 2 a1 + 4 a2 (same as research/d10D7/hexgen2.c) */
static void build_field(void) {
    for (int x = 0; x < 8; x++) for (int y = 0; y < 8; y++) {
        int a[3] = {x & 1, (x >> 1) & 1, (x >> 2) & 1};
        int b[3] = {y & 1, (y >> 1) & 1, (y >> 2) & 1};
        int r[5] = {0, 0, 0, 0, 0};
        for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) r[i + j] ^= a[i] & b[j];
        for (int k = 4; k >= 3; k--) if (r[k]) { r[k] = 0; r[k - 3] ^= 1; r[k - 2] ^= 1; }  /* x^3 = 1 + x */
        MULT[x][y] = (uint8_t)(r[0] | (r[1] << 1) | (r[2] << 2));
    }
    for (int x = 1; x < 8; x++) { int ok = 0; for (int y = 1; y < 8; y++) if (MULT[x][y] == 1) ok = 1;
        if (!ok) { fprintf(stderr, "not a field\n"); exit(1); } }
}

/* B(x,y) over GF(8); addition = XOR */
static inline int Bxy(const uint8_t *x, const uint8_t *y) {
    return MULT[x[0]][y[4]] ^ MULT[x[4]][y[0]] ^ MULT[x[1]][y[5]] ^ MULT[x[5]][y[1]] ^ MULT[x[2]][y[6]] ^ MULT[x[6]][y[2]];
}

static void load(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) { perror(path); exit(2); }
    int32_t h[3]; if (fread(h, 4, 3, f) != 3) { fprintf(stderr, "short header\n"); exit(2); }
    if (h[0] != 8 || h[1] != NP) { fprintf(stderr, "unexpected header q=%d N=%d\n", h[0], h[1]); exit(2); }
    if (fread(LPT, 4, NP * QP, f) != NP * QP) { fprintf(stderr, "short line table\n"); exit(2); }
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
            const uint8_t *y = X + 7 * j;
            if (Bxy(x, y) == 0) {
                if (cnt[i] >= DEG || cnt[j] >= DEG) { fprintf(stderr, "degree above %d\n", DEG); exit(3); }
                NB[(size_t)i * DEG + cnt[i]++] = (uint16_t)j;
                NB[(size_t)j * DEG + cnt[j]++] = (uint16_t)i;
            }
        }
    }
    for (int i = 0; i < NP; i++) if (cnt[i] != DEG) { fprintf(stderr, "vertex %d has degree %d\n", i, cnt[i]); exit(3); }
}

static void selftest(void) {
    int bad = 0;
    for (int i = 0; i < NP; i++) {
        const uint8_t *x = X + 7 * i;
        int lhs = MULT[x[0]][x[4]] ^ MULT[x[1]][x[5]] ^ MULT[x[2]][x[6]];
        if (lhs != MULT[x[3]][x[3]]) bad++;
    }
    printf("quadric violations: %d (expect 0)\n", bad);
    static int32_t pc[NP];
    for (int l = 0; l < NP; l++) for (int k = 0; k < QP; k++) {
        int p = LPT[l * QP + k];
        if (p < 0 || p >= NP || pc[p] >= QP) { printf("bad line table\n"); return; }
        PLT[p * QP + pc[p]++] = l;
    }
    int badpc = 0; for (int p = 0; p < NP; p++) if (pc[p] != QP) badpc++;
    printf("points not on exactly 9 lines: %d (expect 0)\n", badpc);
    static uint8_t d[2 * NP]; static int32_t qu[2 * NP];
    int trials[] = {0, 12345, 37448, 777, 20000};
    for (unsigned t = 0; t < sizeof trials / sizeof trials[0]; t++) {
        int s = trials[t];
        memset(d, 255, 2 * NP);
        int h = 0, tl = 0; d[s] = 0; qu[tl++] = s;
        while (h < tl) {
            int v = qu[h++];
            if (v < NP) { for (int k = 0; k < QP; k++) { int w = NP + PLT[v * QP + k]; if (d[w] == 255) { d[w] = d[v] + 1; qu[tl++] = w; } } }
            else { for (int k = 0; k < QP; k++) { int w = LPT[(v - NP) * QP + k]; if (d[w] == 255) { d[w] = d[v] + 1; qu[tl++] = w; } } }
        }
        int n6 = 0, nperp = 0, mism = 0, maxd = 0;
        for (int y = 0; y < NP; y++) {
            int b = Bxy(X + 7 * s, X + 7 * y), dy = d[y];
            if (dy > maxd) maxd = dy;
            if (dy == 6) n6++;
            if (b != 0 && dy != 6) mism++;
            if (b == 0 && dy == 6) mism++;
            if (b == 0 && y != s) nperp++;
        }
        printf("point %5d: opposite by BFS %d, perpendicular (excl. self) %d, mismatches with B-test %d, max dist %d\n",
               s, n6, nperp, mism, maxd);
    }
}

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

static void init_random(void) {  /* random maximal independent set */
    clear_all();
    static int32_t perm[NP];
    for (int i = 0; i < NP; i++) perm[i] = i;
    for (int i = NP - 1; i > 0; i--) { int j = (int)rndn((uint32_t)i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < NP; i++) { int w = perm[i]; if (!INS[w] && C[w] == 0) add_v(w); }
}

static int pick_min_outside(void) {
    int best = 1 << 30, nc = 0;
    for (int w = 0; w < NP; w++) if (!INS[w]) {
        int c = C[w];
        if (c < best) { best = c; nc = 0; }
        if (c == best) CAND[nc++] = w;
    }
    return CAND[rndn((uint32_t)nc)];
}

static void save_set(const char *fn) {
    for (int i = 0; i < K; i++) for (int j = i + 1; j < K; j++)
        if (Bxy(X + 7 * S[i], X + 7 * S[j]) == 0) { fprintf(stderr, "BUG: conflicting pair %d %d\n", S[i], S[j]); exit(4); }
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *f = fopen(tmp, "w"); if (!f) { perror(tmp); exit(2); }
    for (int i = 0; i < K; i++) fprintf(f, "%d\n", S[i]);
    fclose(f); rename(tmp, fn);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: pov HEXBIN test | pov HEXBIN SEED SECONDS OUTFILE [TA TB STALL PERT RESTART]\n"); return 2; }
    build_field();
    load(argv[1]);
    if (!strcmp(argv[2], "test")) { selftest(); return 0; }
    if (argc < 5) { fprintf(stderr, "missing SECONDS / OUTFILE\n"); return 2; }
    uint64_t seed = strtoull(argv[2], NULL, 10);
    double secs = atof(argv[3]);
    const char *outf = argv[4];
    int TA = argc > 5 ? atoi(argv[5]) : 7;
    int TB = argc > 6 ? atoi(argv[6]) : 10;
    int64_t STALL = argc > 7 ? atoll(argv[7]) : 200000;
    int PERT = argc > 8 ? atoi(argv[8]) : 5;
    int64_t RESTART = argc > 9 ? atoll(argv[9]) : 20000000;
    int ADDFREE = argc > 10 ? atoi(argv[10]) : 0;
    int64_t NOGROW = argc > 11 ? atoll(argv[11]) : 0;
    int64_t SWITCH = argc > 12 ? atoll(argv[12]) : -1;
    int TA2 = argc > 13 ? atoi(argv[13]) : TA, TB2 = argc > 14 ? atoi(argv[14]) : TB;
    int64_t STALL2 = argc > 15 ? atoll(argv[15]) : STALL;
    int PERT2 = argc > 16 ? atoi(argv[16]) : PERT;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    double t0 = now();
    build_nb();
    fprintf(stderr, "neighbour lists built in %.1f s\n", now() - t0);
    for (int i = 0; i < NP; i++) POS[i] = -1;
    init_random();
    epochMax = K; epochMaxIter = 0;
    int bestK = 0;
    int64_t iter = 0, lastImp = 0, lastRestart = 0;
    int bestF = F;
    while (1) {
        iter++;
        if (iter == SWITCH) { TA = TA2; TB = TB2; STALL = STALL2; PERT = PERT2;
            fprintf(stderr, "[switch] at iter %lld: TA=%d TB=%d STALL=%lld PERT=%d K=%d F=%d bestK=%d\n", (long long)iter, TA, TB, (long long)STALL, PERT, K, F, bestK); }
        if ((iter & 4095) == 0 && now() - t0 > secs) break;
        if ((iter & ((1 << 20) - 1)) == 0)
            fprintf(stderr, "[seed %llu] t=%.0fs iter=%lld K=%d F=%d bestK=%d\n", (unsigned long long)seed,
                    now() - t0, (long long)iter, K, F, bestK);
        if (F == 0) {
            if (K > bestK) {
                bestK = K; save_set(outf);
                fprintf(stderr, "[seed %llu] NEW BEST %d at t=%.1fs iter=%lld\n", (unsigned long long)seed, K, now() - t0, (long long)iter);
            }
            int v = pick_min_outside();
            add_v(v);
            bestF = F; lastImp = iter; lastGrow = iter;
            if (K > epochMax) { epochMax = K; epochMaxIter = iter; }
            continue;
        }
        /* u: conflicting member of S with most conflicts, non-tabu */
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
        /* v: outside, non-tabu, minimising conflicts after removing u */
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
        if (ADDFREE && best == 0 && ncand > 0) {  /* a free (conflict-free) outsider: add it, remove nothing */
            int nfree = 0, pick = -1;
            for (int t = 0; t < ncand; t++) { int w = CAND[t]; if (C[w] == 0) { nfree++; if (rndn((uint32_t)nfree) == 0) pick = w; } }
            if (pick >= 0) {
                add_v(pick);
                TOUT[pick] = (int32_t)(iter + 1 + rndn(3));
                if (F < bestF) { bestF = F; lastImp = iter; }
                continue;
            }
        }
        int v;
        if (ncand == 0) { do { v = (int)rndn(NP); } while (INS[v]); }
        else v = CAND[rndn((uint32_t)ncand)];
        rem_v(u);
        add_v(v);
        TIN[u] = (int32_t)(iter + TA + rndn((uint32_t)TB));
        TOUT[v] = (int32_t)(iter + 1 + rndn(3));
        if (F < bestF) { bestF = F; lastImp = iter; }
        if (iter - lastImp > STALL) {  /* perturbation: a few swaps with the least-conflicting random outsiders */
            for (int p = 0; p < PERT; p++) {
                int uu = S[rndn((uint32_t)K)];
                int vv = -1, vc = 1 << 30;
                for (int tries = 0; tries < 20; tries++) {
                    int w = (int)rndn(NP);
                    if (INS[w]) continue;
                    if (C[w] < vc) { vc = C[w]; vv = w; }
                }
                if (vv < 0) continue;
                rem_v(uu); add_v(vv);
                TIN[uu] = (int32_t)(iter + TA + rndn((uint32_t)TB));
                TOUT[vv] = (int32_t)(iter + 1 + rndn(3));
            }
            bestF = F; lastImp = iter;
        }
        if (iter - lastRestart > RESTART || (NOGROW > 0 && iter - lastGrow > NOGROW)) {
            fprintf(stderr, "[epoch %d] end at iter=%lld t=%.0fs: epoch maxK=%d (reached at iter=%lld) bestK=%d\n", epochNo, (long long)iter, now() - t0, epochMax, (long long)epochMaxIter, bestK);
            epochNo++;
            init_random();
            bestF = F; lastImp = iter; lastRestart = iter; lastGrow = iter;
            epochMax = K; epochMaxIter = iter;
            for (int i = 0; i < NP; i++) { TIN[i] = 0; TOUT[i] = 0; }
        }
    }
    fprintf(stderr, "[epoch %d] final epoch maxK=%d (reached at iter=%lld)\n", epochNo, epochMax, (long long)epochMaxIter);
    fprintf(stderr, "[seed %llu] done: bestK=%d iterations=%lld time=%.1fs\n", (unsigned long long)seed, bestK,
            (long long)iter, now() - t0);
    printf("%d\n", bestK);
    return 0;
}
