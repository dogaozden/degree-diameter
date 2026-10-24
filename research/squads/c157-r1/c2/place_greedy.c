/* place_greedy.c: greedy incremental flag placement (squad c157-r1, card c2).
   Adds flags (p_a, l_a), p_a on l_a, one at a time. Step a samples C random candidate flags and keeps the one that
   minimises the signature deficit of research/d15D7/regions.c:
     sigP(u) = {a : d(u,p_a)=4, d(u,l_a)=5}  (points),   sigL(N) = {a : d(N,l_a)=4, d(N,p_a)=5}  (lines),
     deficit = sum over nonempty A of max(0, #points with signature A - #lines with signature A)   (all points, all lines).
   Incremental form: flag a adds bit a to sigP of S'(p) = {u : d(u,p)=4, d(u,l)=5} and to sigL of
   S(l) = {N : d(N,l)=4, d(N,p)=5}, and nothing else. In a generalized hexagon, for a point u with d(u,p)=4 we have
   d(u,l) in {3,5} (triangle inequality, parity, d(p,l)=1), and likewise for lines. Hence
     S'(p) = {u : d(u,p)=4} minus {u : d(u,l)=3},   S(l) = {N : d(N,l)=4} minus {N : d(N,p)=3},
   so two BFS to depth 4 (about 17.6k nodes each) give the sets. Signature classes live in an open-addressing hash table
   (key, #points, #lines). Every point and line stores the table slot of its class. Moving the x points of S'(p) and
   the y lines of S(l) that have old class k to k|bit changes the deficit by
     sum over touched k != 0 of [f(cP-x, cL-y) - f(cP, cL)]  +  sum over touched k of max(0, x-y),
   with f(P,L) = max(0, P-L) and (cP,cL) the old counts of k (the class k|bit was empty before).
   Usage: place_greedy HEXBIN KMAX C SEED OUTPREFIX [checkpoints ...]
     C = random candidates per step. Writes OUTPREFIX<K>.txt ("p l" per line, first K greedy flags) for each checkpoint K
     (default 16 24 32). The greedy is incremental, so the K-prefix equals a K-flag greedy run with the same seed and C.
     At each checkpoint the deficit is also recomputed from scratch (full BFS, regions.c style) as a check. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1;
static int32_t *LP, *PL;                        /* lines -> points (LP), points -> lines (PL), as in regions.c */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "cannot open %s\n", fn); exit(1); }
    q = h[0]; N = h[1]; Q1 = q + 1;
    LP = malloc(4L * N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) { fprintf(stderr, "short hex file\n"); exit(1); }
    fclose(f);
    PL = malloc(4L * N * Q1);
    int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + c[p]++] = l; }
    free(c);
}

/* BFS from point x (isline 0) or line x (isline 1), stopped at distance maxd. hd[v] for v < N is a point, v >= N a line:
   distance, or 255 when farther than maxd. qq receives the reached nodes in BFS order; returns how many. */
static int bfs_lim(int x, int isline, uint8_t *hd, int32_t *qq, int maxd) {
    memset(hd, 255, 2 * (size_t)N);
    int s = isline ? N + x : x; hd[s] = 0; qq[0] = s; int h = 0, t = 1;
    while (h < t) {
        int v = qq[h++]; int d = hd[v];
        if (d >= maxd) continue;
        if (v < N) { const int32_t *r = PL + (size_t)v * Q1; for (int k = 0; k < Q1; k++) { int w = N + r[k]; if (hd[w] == 255) { hd[w] = (uint8_t)(d + 1); qq[t++] = w; } } }
        else { const int32_t *r = LP + (size_t)(v - N) * Q1; for (int k = 0; k < Q1; k++) { int w = r[k]; if (hd[w] == 255) { hd[w] = (uint8_t)(d + 1); qq[t++] = w; } } }
    }
    return t;
}

/* signature classes: open addressing, linear probing, no deletion */
#define HBITS 22
#define HCAP ((uint64_t)1 << HBITS)
#define HMASK (HCAP - 1)
typedef struct { uint64_t key; int32_t cp, cl; } slot_t;   /* cp < 0: unused slot; counts of points and lines */
typedef struct { int32_t x, y; } scr_t;                     /* per-candidate scratch counts, indexed by slot */
static slot_t *HT; static scr_t *SC;
static inline uint64_t hmix(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static uint64_t hslot(uint64_t key) {                       /* find or create the slot of a signature class */
    uint64_t i = hmix(key) & HMASK;
    for (;;) {
        if (HT[i].cp < 0) { HT[i].key = key; HT[i].cp = 0; HT[i].cl = 0; return i; }
        if (HT[i].key == key) return i;
        i = (i + 1) & HMASK;
    }
}

static uint64_t *sigP, *sigL;                  /* signature masks: points, lines */
static uint32_t *slP, *slL;                    /* slot of the current class of each point / line */
static uint8_t *dP, *dL;                       /* BFS distances from the candidate point p / line l, [0,N) points, [N,2N) lines */
static int32_t *qP, *qL;                       /* BFS queues */
static int32_t *SP, *SL; static int nSP, nSL;  /* S'(p) as point ids, S(l) as line ids */
static uint32_t *TCH;                          /* touched slots of the current candidate */

/* fills SP = S'(p) and SL = S(l) for the flag (p,l), p on l */
static void sets_for(int p, int l) {
    int tp = bfs_lim(p, 0, dP, qP, 4), tl = bfs_lim(l, 1, dL, qL, 4);
    nSP = nSL = 0;
    for (int i = 0; i < tp; i++) { int v = qP[i]; if (v < N && dP[v] == 4 && dL[v] != 3) SP[nSP++] = v; }
    for (int i = 0; i < tl; i++) { int v = qL[i]; if (v >= N && dL[v] == 4 && dP[v] != 3) SL[nSL++] = v - N; }
}

/* change of the signature deficit if flag (p,l) were added as the next bit (the value of the new bit is irrelevant) */
static long eval_delta(int p, int l) {
    sets_for(p, l);
    int nt = 0;
    for (int i = 0; i < nSP; i++) { uint32_t s = slP[SP[i]]; if (!SC[s].x && !SC[s].y) TCH[nt++] = s; SC[s].x++; }
    for (int i = 0; i < nSL; i++) { uint32_t s = slL[SL[i]]; if (!SC[s].x && !SC[s].y) TCH[nt++] = s; SC[s].y++; }
    long d = 0;
    for (int i = 0; i < nt; i++) {
        uint32_t s = TCH[i]; long x = SC[s].x, y = SC[s].y;
        if (HT[s].key) {                       /* old class k != 0 loses x points and y lines */
            long fo = HT[s].cp - HT[s].cl; if (fo < 0) fo = 0;
            long fn = ((long)HT[s].cp - x) - ((long)HT[s].cl - y); if (fn < 0) fn = 0;
            d += fn - fo;
        }
        if (x > y) d += x - y;                 /* new class k|bit (empty before) holds x points and y lines */
        SC[s].x = SC[s].y = 0;
    }
    return d;
}

static void apply_flag(int p, int l, uint64_t B) {
    sets_for(p, l);
    for (int i = 0; i < nSP; i++) { int u = SP[i]; uint64_t nw = sigP[u] | B; HT[slP[u]].cp--; uint64_t s = hslot(nw); HT[s].cp++; sigP[u] = nw; slP[u] = (uint32_t)s; }
    for (int i = 0; i < nSL; i++) { int v = SL[i]; uint64_t nw = sigL[v] | B; HT[slL[v]].cl--; uint64_t s = hslot(nw); HT[s].cl++; sigL[v] = nw; slL[v] = (uint32_t)s; }
}

static long table_deficit(void) {
    long d = 0;
    for (uint64_t i = 0; i < HCAP; i++) if (HT[i].cp >= 0 && HT[i].key) { long f = (long)HT[i].cp - HT[i].cl; if (f > 0) d += f; }
    return d;
}

static int cmpu64(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }

/* from scratch: full BFS for every flag, sorted signature lists, regions.c deficit */
static long scratch_deficit(int K, const int *FP, const int *FL) {
    uint8_t *dp = malloc(2 * (size_t)N), *dl = malloc(2 * (size_t)N);
    int32_t *qq = malloc(sizeof(int32_t) * 2 * (size_t)N);
    uint64_t *sp = calloc(N, 8), *sl = calloc(N, 8);
    for (int a = 0; a < K; a++) {
        bfs_lim(FP[a], 0, dp, qq, 99); bfs_lim(FL[a], 1, dl, qq, 99);
        for (int v = 0; v < N; v++) {
            if (dp[v] == 4 && dl[v] == 5) sp[v] |= 1ULL << a;
            if (dl[N + v] == 4 && dp[N + v] == 5) sl[v] |= 1ULL << a;
        }
    }
    qsort(sp, N, 8, cmpu64); qsort(sl, N, 8, cmpu64);
    long deficit = 0; int i = 0, j = 0;
    while (i < N || j < N) {
        uint64_t s = (i < N && (j >= N || sp[i] <= sl[j])) ? sp[i] : sl[j];
        long ci = 0, cj = 0;
        while (i < N && sp[i] == s) { i++; ci++; }
        while (j < N && sl[j] == s) { j++; cj++; }
        if (s && ci > cj) deficit += ci - cj;
    }
    free(dp); free(dl); free(qq); free(sp); free(sl);
    return deficit;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: place_greedy HEXBIN KMAX C SEED OUTPREFIX [checkpoints ...]\n"); return 1; }
    load(argv[1]);
    int KMAX = atoi(argv[2]), C = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    const char *outp = argv[5];
    if (KMAX < 1 || KMAX > 64) { fprintf(stderr, "1 <= KMAX <= 64\n"); return 1; }
    int cps[64], ncp = 0;
    for (int i = 6; i < argc && ncp < 64; i++) cps[ncp++] = atoi(argv[i]);
    if (argc == 6) { cps[0] = 16; cps[1] = 24; cps[2] = 32; ncp = 3; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();

    HT = malloc(sizeof(slot_t) * HCAP); memset(HT, 0xff, sizeof(slot_t) * HCAP);
    SC = calloc(HCAP, sizeof(scr_t));
    sigP = calloc(N, 8); sigL = calloc(N, 8);
    slP = malloc(4 * (size_t)N); slL = malloc(4 * (size_t)N);
    dP = malloc(2 * (size_t)N); dL = malloc(2 * (size_t)N);
    qP = malloc(4 * 2 * (size_t)N); qL = malloc(4 * 2 * (size_t)N);
    SP = malloc(4 * (size_t)N); SL = malloc(4 * (size_t)N); TCH = malloc(4 * 2 * (size_t)N);
    uint64_t s0 = hslot(0); HT[s0].cp = N; HT[s0].cl = N;      /* all points and lines start with the empty signature */
    for (int v = 0; v < N; v++) { slP[v] = (uint32_t)s0; slL[v] = (uint32_t)s0; }

    int *FP = malloc(sizeof(int) * KMAX), *FL = malloc(sizeof(int) * KMAX);
    char *usedP = calloc(N, 1), *usedL = calloc(N, 1);
    long deficit = 0;
    time_t t0 = time(NULL);
    for (int a = 0; a < KMAX; a++) {
        long best = 0; int bp = -1, bl = -1, ncand = 0, nties = 0;
        for (int c = 0; c < C; c++) {
            int p = rndi(N), l = PL[(size_t)p * Q1 + rndi(Q1)];
            if (usedP[p] || usedL[l]) continue;            /* freed points and freed lines must be distinct */
            long d = eval_delta(p, l); ncand++;
            if (bp < 0 || d < best) { best = d; bp = p; bl = l; nties = 1; }
            else if (d == best && rndi(++nties) == 0) { bp = p; bl = l; }
        }
        if (bp < 0) { fprintf(stderr, "no admissible candidate at step %d\n", a + 1); return 1; }
        apply_flag(bp, bl, 1ULL << a);
        deficit += best; FP[a] = bp; FL[a] = bl; usedP[bp] = 1; usedL[bl] = 1;
        long chk = table_deficit();
        fprintf(stderr, "step %2d: flag (%d,%d) delta %ld deficit %ld (table %ld) from %d candidates, %lds\n",
                a + 1, bp, bl, best, deficit, chk, ncand, (long)(time(NULL) - t0));
        if (deficit != chk) { fprintf(stderr, "BUG: incremental deficit differs from table\n"); return 1; }
        for (int k = 0; k < ncp; k++) if (cps[k] == a + 1) {
            char fn[512]; snprintf(fn, sizeof fn, "%s%d.txt", outp, a + 1);
            FILE *f = fopen(fn, "w"); if (!f) { fprintf(stderr, "cannot write %s\n", fn); return 1; }
            for (int i = 0; i <= a; i++) fprintf(f, "%d %d\n", FP[i], FL[i]);
            fclose(f);
            long sd = scratch_deficit(a + 1, FP, FL);
            printf("K=%d deficit(incremental)=%ld deficit(scratch)=%ld file=%s\n", a + 1, deficit, sd, fn);
            fflush(stdout);
        }
    }
    return 0;
}
