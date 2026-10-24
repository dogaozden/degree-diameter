/* place_hall.c: flag placement with a Hall-violation objective (squad c157-r2, card c3).
   Derived from research/squads/c157-r1/c2/place_greedy.c. Geometry and the regions bookkeeping are unchanged:
     sigP(u) = {a : d(u,p_a)=4, d(u,l_a)=5},  sigL(N) = {a : d(N,l_a)=4, d(N,p_a)=5},
     S'(p) = {u : d(u,p)=4, d(u,l)=5},        S(l) = {N : d(N,l)=4, d(N,p)=5}   (two depth-4 BFS per flag).

   Why this objective: a point u can be matched to a line N only if sigL(N) is inside A4(u) and sigP(u) is inside B4(N)
   (cover_match.c). Since A4(u) = sigP(u) for almost all u (points with d(u,p_a)=4, d(u,l_a)=3 have density 0.75 % per
   flag), the matching is nearly "equal signature", and the round-1 deficient points (c6, K = 24) have |sigP| >= 4:
   |sigP| = 3: 2.8 % deficient, 4: 33 %, 5: 76 %, 6+: 77 %. The total sum of |sigP| over points is fixed (q^4 per flag),
   so only the shape of the distribution can be changed: keep |sig| small.
   Objective: F = sum over points u of f(|sigP(u)|) + sum over lines N of f(|sigL(N)|), with f = WTAB (env, comma list
   f(0), f(1), ..., the last entry repeats). Default "0,0,0,1" counts the points and lines with |sig| >= 3.
   A candidate flag adds dF = sum over S'(p) of f(k+1)-f(k) + sum over S(l) of f(k+1)-f(k), k = current popcount.
   Candidate score = 1000*dF + RW*dR, where dR is the regions deficit change of place_greedy (env RW, default 0).
   PASSES (env, default 0): local search after the greedy. A sweep removes each flag in turn and re-places it at the best
   of its old position and C fresh random candidates, so F never increases.

   Usage: place_hall HEXBIN KMAX C SEED OUTPREFIX [checkpoints ...]
     Greedy, C random candidates per step. Without PASSES, OUTPREFIX<K>.txt ("p l" per line, the first K flags) is written at
     each checkpoint (default: KMAX). With PASSES > 0, OUTPREFIX<KMAX>.txt is written after the local search.
     The regions deficit is maintained with the hash table and checked from scratch at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1;
static int32_t *LP, *PL;                        /* lines -> points (LP), points -> lines (PL) */
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

/* BFS from point x (isline 0) or line x (isline 1), stopped at distance maxd (as place_greedy.c) */
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

/* signature classes (for the regions deficit): open addressing, linear probing */
#define HBITS 22
#define HCAP ((uint64_t)1 << HBITS)
#define HMASK (HCAP - 1)
typedef struct { uint64_t key; int32_t cp, cl; } slot_t;   /* cp < 0: unused slot */
typedef struct { int32_t x, y; } scr_t;
static slot_t *HT; static scr_t *SC; static long nslots = 0;
static inline uint64_t hmix(uint64_t x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static uint64_t hslot(uint64_t key) {
    uint64_t i = hmix(key) & HMASK;
    for (;;) {
        if (HT[i].cp < 0) {
            if (++nslots > (long)(HCAP / 4 * 3)) { fprintf(stderr, "signature table too full\n"); exit(1); }
            HT[i].key = key; HT[i].cp = 0; HT[i].cl = 0; return i;
        }
        if (HT[i].key == key) return i;
        i = (i + 1) & HMASK;
    }
}

static uint64_t *sigP, *sigL;                  /* signature masks: points, lines */
static uint32_t *slP, *slL;                    /* table slot of the class of each point / line */
static uint8_t *dP, *dL;                       /* BFS distances from p / l: [0,N) points, [N,2N) lines */
static int32_t *qP, *qL;
static int32_t *SP, *SL; static int nSP, nSL;  /* S'(p) as point ids, S(l) as line ids */
static uint32_t *TCH;

/* the Hall-violation weights: f(k) = WT[min(k, WTN-1)] */
static long WT[65]; static int WTN = 0;
static inline long fw(int k) { return WT[k < WTN ? k : WTN - 1]; }

static void sets_for(int p, int l) {
    int tp = bfs_lim(p, 0, dP, qP, 4), tl = bfs_lim(l, 1, dL, qL, 4);
    nSP = nSL = 0;
    for (int i = 0; i < tp; i++) { int v = qP[i]; if (v < N && dP[v] == 4 && dL[v] != 3) SP[nSP++] = v; }
    for (int i = 0; i < tl; i++) { int v = qL[i]; if (v >= N && dL[v] == 4 && dP[v] != 3) SL[nSL++] = v - N; }
}

/* change of F and of the regions deficit if flag (p,l) were added as a new bit (its value is irrelevant) */
static long eval_delta(int p, int l, long *dRout) {
    sets_for(p, l);
    long dF = 0;
    for (int i = 0; i < nSP; i++) { int k = __builtin_popcountll(sigP[SP[i]]); dF += fw(k + 1) - fw(k); }
    for (int i = 0; i < nSL; i++) { int k = __builtin_popcountll(sigL[SL[i]]); dF += fw(k + 1) - fw(k); }
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
        if (x > y) d += x - y;                 /* new class (empty before, the bit is new) */
        SC[s].x = SC[s].y = 0;
    }
    *dRout = d;
    return dF;
}

/* set (add=1) or clear (add=0) bit B of the signatures of S'(p) and S(l); keeps the class table current */
static void update_flag(int p, int l, uint64_t B, int add) {
    sets_for(p, l);
    for (int i = 0; i < nSP; i++) {
        int u = SP[i]; uint64_t nw = add ? (sigP[u] | B) : (sigP[u] & ~B);
        HT[slP[u]].cp--; uint64_t s = hslot(nw); HT[s].cp++; sigP[u] = nw; slP[u] = (uint32_t)s;
    }
    for (int i = 0; i < nSL; i++) {
        int v = SL[i]; uint64_t nw = add ? (sigL[v] | B) : (sigL[v] & ~B);
        HT[slL[v]].cl--; uint64_t s = hslot(nw); HT[s].cl++; sigL[v] = nw; slL[v] = (uint32_t)s;
    }
}

static long table_deficit(void) {
    long d = 0;
    for (uint64_t i = 0; i < HCAP; i++) if (HT[i].cp >= 0 && HT[i].key) { long f = (long)HT[i].cp - HT[i].cl; if (f > 0) d += f; }
    return d;
}

static long total_F(void) {
    long F = 0;
    for (int v = 0; v < N; v++) F += fw(__builtin_popcountll(sigP[v])) + fw(__builtin_popcountll(sigL[v]));
    return F;
}

static void histo(const char *name, const uint64_t *sg) {
    long h[9] = {0};
    for (int v = 0; v < N; v++) { int k = __builtin_popcountll(sg[v]); h[k > 8 ? 8 : k]++; }
    fprintf(stderr, "%s |sig| hist 0..8+:", name); for (int k = 0; k < 9; k++) fprintf(stderr, " %ld", h[k]); fprintf(stderr, "\n");
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

static void write_flags(const char *fn, int K, const int *FP, const int *FL) {
    FILE *f = fopen(fn, "w"); if (!f) { fprintf(stderr, "cannot write %s\n", fn); exit(1); }
    for (int i = 0; i < K; i++) fprintf(f, "%d %d\n", FP[i], FL[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: place_hall HEXBIN KMAX C SEED OUTPREFIX [checkpoints ...]\n"); return 1; }
    load(argv[1]);
    int KMAX = atoi(argv[2]), C = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    const char *outp = argv[5];
    if (KMAX < 1 || KMAX > 64) { fprintf(stderr, "1 <= KMAX <= 64\n"); return 1; }
    int cps[64], ncp = 0;
    for (int i = 6; i < argc && ncp < 64; i++) cps[ncp++] = atoi(argv[i]);
    if (ncp == 0) cps[ncp++] = KMAX;
    const char *wt = getenv("WTAB"); if (!wt) wt = "0,0,0,1";
    char *wcopy = strdup(wt);
    for (char *tok = strtok(wcopy, ","); tok && WTN < 64; tok = strtok(NULL, ",")) WT[WTN++] = atol(tok);
    if (!WTN) { fprintf(stderr, "empty WTAB\n"); return 1; }
    long RW = getenv("RW") ? atol(getenv("RW")) : 0;
    int PASSES = getenv("PASSES") ? atoi(getenv("PASSES")) : 0;
    fprintf(stderr, "WTAB f(0..%d) =", WTN - 1); for (int k = 0; k < WTN; k++) fprintf(stderr, " %ld", WT[k]);
    fprintf(stderr, "  RW %ld  PASSES %d  C %d  seed %llu\n", RW, PASSES, C, (unsigned long long)seed);
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
        long best = 0, bdF = 0, bdR = 0; int bp = -1, bl = -1, ncand = 0, nties = 0;
        for (int c = 0; c < C; c++) {
            int p = rndi(N), l = PL[(size_t)p * Q1 + rndi(Q1)];
            if (usedP[p] || usedL[l]) continue;            /* freed points and freed lines must be distinct */
            long dR, dF = eval_delta(p, l, &dR); ncand++;
            long sc = 1000 * dF + RW * dR;
            if (bp < 0 || sc < best) { best = sc; bp = p; bl = l; bdF = dF; bdR = dR; nties = 1; }
            else if (sc == best && rndi(++nties) == 0) { bp = p; bl = l; bdF = dF; bdR = dR; }
        }
        if (bp < 0) { fprintf(stderr, "no admissible candidate at step %d\n", a + 1); return 1; }
        update_flag(bp, bl, 1ULL << a, 1);
        deficit += bdR; FP[a] = bp; FL[a] = bl; usedP[bp] = 1; usedL[bl] = 1;
        long F = total_F(), chk = table_deficit();
        fprintf(stderr, "step %2d: flag (%d,%d) dF %ld F %ld regions deficit %ld (table %ld) from %d candidates, %lds\n",
                a + 1, bp, bl, bdF, F, deficit, chk, ncand, (long)(time(NULL) - t0));
        if (deficit != chk) { fprintf(stderr, "BUG: incremental deficit differs from table\n"); return 1; }
        if (!PASSES) for (int k = 0; k < ncp; k++) if (cps[k] == a + 1) {
            char fn[512]; snprintf(fn, sizeof fn, "%s%d.txt", outp, a + 1);
            write_flags(fn, a + 1, FP, FL);
            long sd = scratch_deficit(a + 1, FP, FL);
            printf("K=%d F=%ld deficit(incremental)=%ld deficit(scratch)=%ld file=%s\n", a + 1, F, deficit, sd, fn);
            fflush(stdout);
        }
    }
    if (PASSES > 0) {
        for (int pass = 1; pass <= PASSES; pass++) {
            int moved = 0;
            for (int a = 0; a < KMAX; a++) {
                int op = FP[a], ol = FL[a];
                update_flag(op, ol, 1ULL << a, 0);
                usedP[op] = 0; usedL[ol] = 0;
                long dR0, dF0 = eval_delta(op, ol, &dR0);
                long best = 1000 * dF0 + RW * dR0, bdR = dR0; int bp = op, bl = ol;
                for (int c = 0; c < C; c++) {
                    int p = rndi(N), l = PL[(size_t)p * Q1 + rndi(Q1)];
                    if (usedP[p] || usedL[l]) continue;
                    long dR, dF = eval_delta(p, l, &dR);
                    long sc = 1000 * dF + RW * dR;
                    if (sc < best) { best = sc; bp = p; bl = l; bdR = dR; }
                }
                update_flag(bp, bl, 1ULL << a, 1);
                FP[a] = bp; FL[a] = bl; usedP[bp] = 1; usedL[bl] = 1;
                if (bp != op || bl != ol) moved++;
            }
            deficit = table_deficit();
            fprintf(stderr, "pass %d: moved %d flags, F %ld, regions deficit %ld (%lds)\n",
                    pass, moved, total_F(), deficit, (long)(time(NULL) - t0));
            if (!moved) break;
        }
        char fn[512]; snprintf(fn, sizeof fn, "%s%d.txt", outp, KMAX);
        write_flags(fn, KMAX, FP, FL);
        long sd = scratch_deficit(KMAX, FP, FL);
        printf("K=%d F=%ld deficit(incremental)=%ld deficit(scratch)=%ld file=%s\n", KMAX, total_F(), table_deficit(), sd, fn);
    }
    histo("points", sigP); histo("lines", sigL);
    return 0;
}
