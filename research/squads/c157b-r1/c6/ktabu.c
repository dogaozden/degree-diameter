/* c6: k-fixed tabu / penalty search for a set of points of H(11) with no two on a common line.
 * K chosen points; penalty = sum over lines of max(0, chosen_on_line - 1).
 * occ[x] = number of lines through x that contain a chosen point other than x.
 *   chosen p: removing p changes penalty by -occ[p];  unchosen q: adding q changes it by +occ[q].
 *   swap p out, q in: delta = occ[q] - occ[p] - corr, corr = 1 iff p,q share a line on which p is the only chosen point.
 * Move: p = max-occ non-tabu chosen point; q = min-occ non-tabu unchosen point (with corr-aware candidates on
 * p's lines). Tabu: a removed point may not be re-added for ~TT iterations, an added point may not be removed for
 * ~TT/2. Aspiration if the move gives a penalty below the best seen at this K. When penalty = 0: save, K++.
 * usage: ktabu HEXBIN RH K0 SEED SECONDS DROP TT NOISE OUT
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int N, L;
static int32_t *lp, *pl, *bkpos, *Sl, *Spos, *tAdd, *tRem;
static uint8_t *cnt, *inS, *occ;
static int32_t *bk[13];
static int bksz[13];
static int nS = 0;
static long conf = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

/* buckets of UNCHOSEN points indexed by occ value */
static inline void bk_ins(int x) { int v = occ[x]; bkpos[x] = bksz[v]; bk[v][bksz[v]++] = x; }
static inline void bk_del(int x) { int v = occ[x]; int i = bkpos[x]; int last = bk[v][--bksz[v]]; bk[v][i] = last; bkpos[last] = i; }
static inline void occ_inc(int x, int d) { bk_del(x); occ[x] += (uint8_t)d; bk_ins(x); }  /* x unchosen */

static void add_pt(int y) {
    bk_del(y);
    inS[y] = 1;
    Spos[y] = nS; Sl[nS++] = y;
    for (int k = 0; k < 12; k++) {
        int l = pl[y * 12 + k];
        int c = cnt[l];
        if (c >= 1) conf++;
        for (int j = 0; j < 12; j++) {
            int x = lp[l * 12 + j];
            if (x == y) continue;
            if (inS[x]) { if (c == 1) occ[x]++; }
            else if (c == 0) occ_inc(x, 1);
        }
        cnt[l] = (uint8_t)(c + 1);
    }
}

static void rem_pt(int y) {
    int i = Spos[y]; int last = Sl[--nS]; Sl[i] = last; Spos[last] = i;
    inS[y] = 0;
    bk_ins(y);                       /* occ[y] itself is unchanged by its own removal */
    for (int k = 0; k < 12; k++) {
        int l = pl[y * 12 + k];
        int c = cnt[l];              /* includes y */
        if (c >= 2) conf--;
        for (int j = 0; j < 12; j++) {
            int x = lp[l * 12 + j];
            if (x == y) continue;
            if (inS[x]) { if (c == 2) occ[x]--; }
            else if (c == 1) occ_inc(x, -1);
        }
        cnt[l] = (uint8_t)(c - 1);
    }
}

static void save_set(const char *path) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *g = fopen(tmp, "w"); if (!g) { perror("save"); return; }
    for (int i = 0; i < nS; i++) fprintf(g, "%d\n", Sl[i]);
    fclose(g); rename(tmp, path);
}

#ifdef CHECK
static void check_all(const char *where, long it) {
    uint8_t *c2 = calloc(L, 1); long cf = 0; int ns = 0;
    for (int x = 0; x < N; x++) ns += inS[x];
    if (ns != nS) { fprintf(stderr, "nS mismatch %s it=%ld\n", where, it); exit(2); }
    for (int i = 0; i < nS; i++) { int x = Sl[i]; if (!inS[x] || Spos[x] != i) { fprintf(stderr, "Sl mismatch\n"); exit(2);} for (int k = 0; k < 12; k++) c2[pl[x * 12 + k]]++; }
    for (int l = 0; l < L; l++) { if (c2[l] != cnt[l]) { fprintf(stderr, "cnt mismatch %s it=%ld\n", where, it); exit(2); } if (c2[l] >= 1) cf += c2[l] - 1; }
    if (cf != conf) { fprintf(stderr, "conf mismatch %s it=%ld %ld vs %ld\n", where, it, cf, conf); exit(2); }
    for (int x = 0; x < N; x++) {
        int o = 0;
        for (int k = 0; k < 12; k++) { int l = pl[x * 12 + k]; if ((int)c2[l] - inS[x] >= 1) o++; }
        if (o != occ[x]) { fprintf(stderr, "occ mismatch %s it=%ld x=%d %d vs %d\n", where, it, x, o, occ[x]); exit(2); }
        if (!inS[x] && bk[occ[x]][bkpos[x]] != x) { fprintf(stderr, "bucket mismatch x=%d\n", x); exit(2); }
    }
    free(c2);
}
#endif

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: ktabu HEXBIN RH K0 SEED SECONDS DROP TT NOISE OUT\n"); return 1; }
    const char *hexf = argv[1], *rhf = argv[2];
    int K0 = atoi(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
    double secs = atof(argv[5]); int drop = atoi(argv[6]); int TT = atoi(argv[7]);
    double noise = atof(argv[8]); const char *out = argv[9];
    if (TT < 2) TT = 2;
    rs ^= seed * 0x2545F4914F6CDD1DULL + 12345ULL; if (!rs) rs = 1; for (int i = 0; i < 20; i++) rnd64();

    FILE *f = fopen(hexf, "rb"); if (!f) { perror("hex"); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int qq0 = hdr[0]; N = hdr[1]; L = hdr[2];
    if (qq0 != 11 || N != 177156 || L != 177156) { fprintf(stderr, "bad header\n"); return 1; }
    lp = malloc(sizeof(int32_t) * 12 * (size_t)L);
    if (fread(lp, 4, 12 * (size_t)L, f) != 12 * (size_t)L) { fprintf(stderr, "short read\n"); return 1; }
    fclose(f);
    pl = malloc(sizeof(int32_t) * 12 * (size_t)N);
    int *deg = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < 12; k++) {
        int p = lp[l * 12 + k];
        if (deg[p] >= 12) { fprintf(stderr, "degree error\n"); return 1; }
        pl[p * 12 + deg[p]++] = l;
    }
    free(deg);

    cnt = calloc(L, 1); inS = calloc(N, 1); occ = calloc(N, 1);
    tAdd = calloc(N, sizeof(int32_t)); tRem = calloc(N, sizeof(int32_t));
    Sl = malloc(sizeof(int32_t) * N); Spos = malloc(sizeof(int32_t) * N); bkpos = malloc(sizeof(int32_t) * N);
    for (int v = 0; v <= 12; v++) bk[v] = malloc(sizeof(int32_t) * N);
    bksz[0] = N; for (int x = 0; x < N; x++) { bk[0][x] = x; bkpos[x] = x; }

    /* RH start */
    FILE *rf = fopen(rhf, "r"); if (!rf) { perror("RH"); return 1; }
    int v; int nrh = 0;
    while (fscanf(rf, "%d", &v) == 1) { if (v < 0 || v >= N || inS[v]) { fprintf(stderr, "bad RH id %d\n", v); return 1; } add_pt(v); nrh++; }
    fclose(rf);
    printf("loaded RH: %d points, penalty %ld\n", nrh, conf); fflush(stdout);
    for (int i = 0; i < drop && nS > 0; i++) rem_pt(Sl[rndn(nS)]);
    while (nS < K0) { int x; do { x = rndn(N); } while (inS[x]); add_pt(x); }
    printf("start K=%d penalty=%ld\n", nS, conf); fflush(stdout);

    long it = 0; double t0 = now_s(), tlast = t0;
    long bestConfK = conf;
    int bestK = 0;
    while (1) {
        if (conf == 0) {
            save_set(out); bestK = nS;
            printf("FEASIBLE K=%d it=%ld t=%.1f\n", nS, it, now_s() - t0); fflush(stdout);
            int q = -1;
            for (int b = 0; b <= 12 && q < 0; b++) if (bksz[b]) q = bk[b][rndn(bksz[b])];
            add_pt(q);
            bestConfK = conf;
            continue;
        }
        if ((it & 4095) == 0) {
            double t = now_s();
            if (t - t0 > secs) break;
            if (t - tlast >= 15) { printf("  it=%ld t=%.0f K=%d penalty=%ld bestAtK=%ld\n", it, t - t0, nS, conf, bestConfK); fflush(stdout); tlast = t; }
        }
#ifdef CHECK
        if (it % 500 == 0) check_all("periodic", it);
#endif
        it++;

        /* choose p: max occ among non-tabu chosen points (random ties) */
        int p = -1, pv = -1, ties = 0;
        for (int i = 0; i < nS; i++) {
            int x = Sl[i];
            if (tRem[x] > it) continue;
            int vv = occ[x];
            if (vv > pv) { pv = vv; p = x; ties = 1; }
            else if (vv == pv) { ties++; if (rndn(ties) == 0) p = x; }
        }
        int noisy = (noise > 0 && rnd01() < noise);
        if (p < 0 || noisy) { p = Sl[rndn(nS)]; pv = occ[p]; }

        int qq = -1;
        if (noisy) {
            do { qq = rndn(N); } while (inS[qq] || tAdd[qq] > it);
        } else {
            /* generic: lowest occ bucket with an admissible (non-tabu or aspirated) point */
            int g = -1, gb = -1;
            for (int b = 0; b <= 12 && g < 0; b++) {
                int sz = bksz[b]; if (!sz) continue;
                int asp = (conf + b - pv < bestConfK);
                int x = -1;
                for (int t = 0; t < 6 && x < 0; t++) { int y = bk[b][rndn(sz)]; if (asp || tAdd[y] <= it) x = y; }
                if (x < 0) {
                    int ok = 0;
                    for (int i = 0; i < sz; i++) { int y = bk[b][i]; if (asp || tAdd[y] <= it) { ok++; if (rndn(ok) == 0) x = y; } }
                }
                if (x >= 0) { g = x; gb = b; }
            }
            /* corrected: unchosen points on lines through p that carry no other chosen point (corr = 1) */
            int c2 = -1, c2v = 1 << 20;
            for (int k = 0; k < 12; k++) {
                int l = pl[p * 12 + k];
                if (cnt[l] != 1) continue;
                for (int j = 0; j < 12; j++) {
                    int x = lp[l * 12 + j];
                    if (x == p) continue;
                    int vv = occ[x] - 1;
                    int asp = (conf + vv - pv < bestConfK);
                    if (!asp && tAdd[x] > it) continue;
                    if (vv < c2v || (vv == c2v && rndn(2) == 0)) { c2v = vv; c2 = x; }
                }
            }
            if (c2 >= 0 && (g < 0 || c2v < gb)) qq = c2;
            else if (g >= 0) qq = g;
            else { do { qq = rndn(N); } while (inS[qq] || tAdd[qq] > it); }
        }

        rem_pt(p);
        add_pt(qq);
        tAdd[p] = (int32_t)(it + TT + rndn(TT + 1));
        tRem[qq] = (int32_t)(it + TT / 2 + rndn(TT / 2 + 1));
        if (conf < bestConfK) bestConfK = conf;
    }
    printf("END it=%ld t=%.1f bestFeasibleK=%d finalK=%d finalPenalty=%ld\n", it, now_s() - t0, bestK, nS, conf);
    fflush(stdout);
    return 0;
}
