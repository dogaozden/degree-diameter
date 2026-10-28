/* e16_dom.c: K disjoint 4-dominating classes of LINES of H(q) (q = 7), by min-conflicts local search.
   Card e16 (wildcard), polylev squad r2. Written from scratch for this card.

   A class B is 4-dominating when every line L has a member of B at incidence distance <= 4 (members of B may be any
   lines, not only pencils). Classes are grown one at a time: a class is activated (all N pairs (class, line) are
   undominated), then a focused local search repairs one random undominated pair (k, w) by moving one of the lines of
   ball(w) into class k. Candidate moves are scored by the exact cost change (sampled candidates), with tabu.
   When all active pairs are dominated, redundant members are pruned in place, the colouring is written, and the next
   class is activated. Stops on the wall clock or when no new valid K has appeared for STALL seconds.

   Usage: e16_dom HEX SEED WALL INIT(pencil|empty) KMAX M STALL OUT
     HEX: hexagon file (int32 q, N, L; L*(q+1) int32 point ids; N*7 uint8 coordinates)
     WALL, STALL: wall-clock seconds; M: sampled candidates per move (e.g. 48); OUT: int32 colour per line (-1 free)
   The output file is written each time a larger valid K is reached. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1, BS, Kmax, Kact = 0, M = 48, TT = 7, NOISE = 1;
static int32_t *LP, *PL;
static uint16_t *ball;     /* N x BS: lines at distance <= 4 from each line (itself included) */
static int16_t *col;       /* N: class of each line, -1 free */
static int *csize;         /* Kmax */
static uint16_t *cnt;      /* Kmax x N: members of class k in ball(w) */
static int32_t *U, *posU;  /* undominated pairs id = k*N + w, as a list with positions */
static long nU = 0, over = 0;   /* over = sum over classes of max(0, size - CAP) */
static int CAP = 1000000, LAMBDA = 2;   /* size cap per class (soft: each unit above it costs LAMBDA) */
static long *tabu;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_ball(int x, uint16_t *out, int *mark, int *stamp) {
    int c = 0; (*stamp)++; out[c++] = (uint16_t)x; mark[x] = *stamp;
    int lo = 0, hi = 1;
    for (int round = 0; round < 2; round++) {          /* distance 2, then distance 4 */
        for (int i = lo; i < hi; i++) {
            int L = out[i];
            for (int a = 0; a < Q1; a++) { int p = LP[L * Q1 + a];
                for (int b = 0; b < Q1; b++) { int M2 = PL[p * Q1 + b];
                    if (mark[M2] != *stamp) { mark[M2] = *stamp; out[c++] = (uint16_t)M2; } } }
        }
        lo = hi; hi = c;
    }
    if (c != BS) { fprintf(stderr, "ball size %d, expected %d\n", c, BS); exit(1); }
}

static inline void mark_dom(int id) { int p = posU[id]; int last = U[--nU]; U[p] = last; posU[last] = p; posU[id] = -1; }
static inline void mark_und(int id) { posU[id] = (int32_t)nU; U[nU++] = id; }
static inline void inc(int k, int w) { size_t id = (size_t)k * N + w; if (cnt[id] == 0) mark_dom((int)id); cnt[id]++; }
static inline void dec(int k, int w) { size_t id = (size_t)k * N + w; cnt[id]--; if (cnt[id] == 0) mark_und((int)id); }

static void assign(int x, int k) {   /* move line x to class k (k = -1: free it) */
    int a = col[x];
    if (a == k) return;
    const uint16_t *b = ball + (size_t)x * BS;
    if (a >= 0) { for (int t = 0; t < BS; t++) dec(a, b[t]); if (csize[a] > CAP) over--; csize[a]--; }
    if (k >= 0) { for (int t = 0; t < BS; t++) inc(k, b[t]); csize[k]++; if (csize[k] > CAP) over++; }
    col[x] = (int16_t)k;
}

static int delta(int x, int k) {     /* cost change (new undominated minus newly dominated) if x moves to k */
    int a = col[x];
    const uint16_t *b = ball + (size_t)x * BS, *ck = cnt + (size_t)k * N;
    int gain = 0, loss = 0;
    for (int t = 0; t < BS; t++) if (ck[b[t]] == 0) gain++;
    if (a >= 0) { const uint16_t *ca = cnt + (size_t)a * N; for (int t = 0; t < BS; t++) if (ca[b[t]] == 1) loss++; }
    int pen = 0; if (csize[k] >= CAP) pen += LAMBDA; if (a >= 0 && csize[a] > CAP) pen -= LAMBDA;
    return loss - gain + pen;
}

static void activate(int k) { for (int w = 0; w < N; w++) mark_und(k * N + w); Kact = k + 1; }

static void prune(void) {            /* free members whose removal keeps every ball of their class dominated */
    int *ord = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) ord[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
    for (int i = 0; i < N; i++) { int x = ord[i], a = col[x]; if (a < 0) continue;
        const uint16_t *b = ball + (size_t)x * BS; int ok = 1;
        for (int t = 0; t < BS && ok; t++) if (cnt[(size_t)a * N + b[t]] < 2) ok = 0;
        if (ok) assign(x, -1); }
    free(ord);
}

static void write_sol(const char *path, int K) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb"); if (!f) return;
    int32_t *o = malloc(sizeof(int32_t) * N); for (int x = 0; x < N; x++) o[x] = col[x];
    fwrite(o, 4, N, f); fclose(f); free(o); rename(tmp, path);
    fprintf(stderr, "wrote K=%d to %s\n", K, path);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: e16_dom HEX SEED WALL INIT KMAX M STALL OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "no hex\n"); return 1; }
    q = h[0]; N = h[1]; Q1 = q + 1;
    if (h[2] != N) { fprintf(stderr, "L != N\n"); return 1; }
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) { fprintf(stderr, "short hex\n"); return 1; }
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *fill = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[l * Q1 + a]; PL[p * Q1 + fill[p]++] = l; }
    for (int p = 0; p < N; p++) if (fill[p] != Q1) { fprintf(stderr, "bad incidence\n"); return 1; }
    BS = 1 + q * (q + 1) + q * q * q * (q + 1);
    uint64_t seed = strtoull(argv[2], NULL, 10); rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double WALL = atof(argv[3]); int pencil_init = strcmp(argv[4], "pencil") == 0;
    Kmax = atoi(argv[5]); M = atoi(argv[6]); double STALL = atof(argv[7]); const char *OUT = argv[8];
    if (argc > 9) CAP = atoi(argv[9]);
    if (argc > 10) LAMBDA = atoi(argv[10]);

    ball = malloc(sizeof(uint16_t) * (size_t)N * BS);
    { int *mark = calloc(N, sizeof(int)); int stamp = 0;
      for (int x = 0; x < N; x++) build_ball(x, ball + (size_t)x * BS, mark, &stamp); free(mark); }
    col = malloc(sizeof(int16_t) * N); for (int x = 0; x < N; x++) col[x] = -1;
    csize = calloc(Kmax, sizeof(int));
    cnt = calloc((size_t)Kmax * N, sizeof(uint16_t));
    U = malloc(sizeof(int32_t) * (size_t)Kmax * N); posU = malloc(sizeof(int32_t) * (size_t)Kmax * N);
    tabu = calloc(N, sizeof(long));
    fprintf(stderr, "q=%d N=%d BS=%d Kmax=%d M=%d init=%s\n", q, N, BS, Kmax, M, pencil_init ? "pencil" : "empty");

    double t0 = now(), lastvalid = t0, lastprint = t0;
    int bestK = 0;
    if (pencil_init) {   /* greedy partial ovoid of points: pencils of pairwise non-collinear points as first classes */
        int *ord = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) ord[i] = i;
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = ord[i]; ord[i] = ord[j]; ord[j] = t; }
        for (int i = 0; i < N && Kact < Kmax; i++) { int z = ord[i], ok = 1;
            for (int b = 0; b < Q1 && ok; b++) if (col[PL[z * Q1 + b]] >= 0) ok = 0;
            if (!ok) continue;
            int k = Kact; activate(k);
            for (int b = 0; b < Q1; b++) assign(PL[z * Q1 + b], k); }
        free(ord);
        fprintf(stderr, "pencil init: %d classes, undominated %ld\n", Kact, nU);
    }
    if (nU == 0 && over == 0 && Kact > 0) { prune(); bestK = Kact; write_sol(OUT, bestK); }
    if (Kact == 0 || nU == 0) { if (Kact < Kmax) activate(Kact); }
    long it = 0;
    while (1) {
        if (nU == 0 && over > 0) {   /* kick: free one member of an oversized class */
            int s0 = rnd() % N;
            for (int i = 0; i < N; i++) { int x = (s0 + i) % N; if (col[x] >= 0 && csize[col[x]] > CAP) { assign(x, -1); break; } }
            continue;
        }
        if (nU == 0) {
            if (Kact > bestK) { bestK = Kact; prune(); write_sol(OUT, bestK); lastvalid = now(); }
            if (Kact >= Kmax) break;
            activate(Kact);
            continue;
        }
        it++;
        if ((it & 255) == 0) {
            double t = now();
            if (t - t0 > WALL) break;
            if (t - lastvalid > STALL) break;
            if (t - lastprint > 10) { lastprint = t;
                long freeN = 0; for (int x = 0; x < N; x++) if (col[x] < 0) freeN++;
                fprintf(stderr, "%.0fs it %ld Kact %d undominated %ld over %ld free %ld bestK %d\n", t - t0, it, Kact, nU, over, freeN, bestK); }
        }
        int pick = U[rnd() % nU]; int k = pick / N, w = pick % N;
        int bestx = -1, bestd = 1 << 30, ties = 0;
        const uint16_t *bw = ball + (size_t)w * BS;
        int hard = LAMBDA >= 1000;   /* hard cap: never move a line into a full class */
        if ((rnd() % 100) < (uint64_t)NOISE) { int x = bw[rnd() % BS]; if (!(hard && csize[k] >= CAP)) bestx = x; }
        else for (int s = 0; s < M; s++) {
            int x = bw[rnd() % BS];
            if (tabu[x] > it) continue;
            if (hard && csize[k] >= CAP) continue;
            int d = delta(x, k);
            if (d < bestd) { bestd = d; bestx = x; ties = 1; }
            else if (d == bestd && rnd() % (++ties) == 0) bestx = x;
        }
        if (bestx < 0) continue;
        assign(bestx, k);
        tabu[bestx] = it + TT + (long)(rnd() % TT);
    }
    fprintf(stderr, "done: it %ld bestK %d Kact %d undominated %ld time %.0fs\n", it, bestK, Kact, nU, now() - t0);
    printf("bestK %d\n", bestK);
    return 0;
}
