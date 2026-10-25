/* sa.c: squad round 3, card c8 (WILDCARD): fixed-size penalty simulated annealing on the points of H(11).
   A point set S (|S| = k) is opposite-pairwise iff no two points are perpendicular (B(x,y) = 0 mod 11).
   State: k points; cost = number of perpendicular pairs inside S.
   Move: remove a point y of S (tournament on conflict count, tabu), add a low-conflict point x outside S
   (sampled from the buckets of points with few conflicts; tabu on re-adding removed points).
   Delta = (cnt[x] - [x,y perpendicular]) - cnt[y];  Metropolis acceptance at temperature T.
   When cost = 0 the set is saved (valid) and k is increased by adding a minimum-conflict point.

   usage: sa HEXFILE INIT_IDX|- OUT_IDX CPU_SECONDS SEED TEMP
   INIT_IDX: a feasible set (pairwise opposite) or '-' for a random greedy start.
   Writes OUT_IDX every time a larger feasible set is reached. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define QQ 11
#define KK 12
#define PMAX 16200
#define LMAX 6

static int N, NL;
static int32_t *lp, *pl;
static uint8_t *co;
static int8_t *wd;
static int32_t *cnt;          /* cnt[x] = #{s in S, s != x, B(x,s) = 0} */
static uint8_t *inS;
static int32_t *S, *spos; static int k = 0;
static int64_t cost = 0;
static int32_t *bk[LMAX + 1], bsz[LMAX + 1], *bpos; static int8_t *bcat;
static int64_t *tabu_add, *tabu_rem;
static int32_t tbuf[PMAX];
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static inline int Bxy(int x, int y) {
    const int8_t *w = wd + 7L * x; const uint8_t *v = co + 7L * y;
    int s = w[0]*v[0] + w[1]*v[1] + w[2]*v[2] + w[3]*v[3] + w[4]*v[4] + w[5]*v[5] + w[6]*v[6];
    s %= QQ; return s < 0 ? s + QQ : s;
}

/* all y != x with B(x,y) = 0 (16104 of them), by the paths x-L1-p1-L2-p2 */
static int perp(int x, int32_t *out) {
    int n = 0;
    for (int a = 0; a < KK; a++) {
        int L1 = pl[(size_t)x * KK + a];
        for (int b = 0; b < KK; b++) {
            int p1 = lp[(size_t)L1 * KK + b];
            if (p1 == x) continue;
            out[n++] = p1;
            for (int d = 0; d < KK; d++) {
                int L2 = pl[(size_t)p1 * KK + d];
                if (L2 == L1) continue;
                for (int e = 0; e < KK; e++) {
                    int p2 = lp[(size_t)L2 * KK + e];
                    if (p2 != p1) out[n++] = p2;
                }
            }
        }
    }
    return n;
}

static inline void bk_remove(int x) {
    int c = bcat[x]; if (c < 0) return;
    int idx = bpos[x]; int last = bk[c][--bsz[c]];
    bk[c][idx] = last; bpos[last] = idx; bpos[x] = -1; bcat[x] = -1;
}
static inline void bk_insert(int x, int c) { bcat[x] = (int8_t)c; bpos[x] = bsz[c]; bk[c][bsz[c]++] = x; }
static inline void bump(int x, int d) {
    if (!inS[x]) { bk_remove(x); cnt[x] += d; if (cnt[x] <= LMAX) bk_insert(x, cnt[x]); }
    else cnt[x] += d;
}
static void addR(int x) {          /* x not in S */
    bk_remove(x);
    cost += cnt[x];
    inS[x] = 1; spos[x] = k; S[k++] = x;
    int n = perp(x, tbuf);
    for (int i = 0; i < n; i++) bump(tbuf[i], +1);
}
static void delR(int y) {          /* y in S */
    int p = spos[y]; int last = S[--k]; S[p] = last; spos[last] = p; spos[y] = -1;
    inS[y] = 0;
    cost -= cnt[y];
    int n = perp(y, tbuf);
    for (int i = 0; i < n; i++) bump(tbuf[i], -1);
    if (cnt[y] <= LMAX) bk_insert(y, cnt[y]);
}

static int write_set(const char *fn, const char *tag) {
    FILE *f = fopen(fn, "w"); if (!f) return 0;
    fprintf(f, "# %s: %d points, pairwise opposite (squad r3 c8 sa, H(11) point indices)\n", tag, k);
    for (int i = 0; i < k; i++) fprintf(f, "%d\n", S[i]);
    fclose(f); return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: sa HEXFILE INIT_IDX|- OUT_IDX CPU_SECONDS SEED TEMP\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) return 1;
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0]; N = hdr[1]; NL = hdr[2];
    if (q != QQ || KK != q + 1) { fprintf(stderr, "unexpected q %d\n", q); return 1; }
    lp = malloc(4L * NL * KK); if (fread(lp, 4, (size_t)NL * KK, f) != (size_t)NL * KK) return 1;
    co = malloc(7L * N); if (fread(co, 1, 7L * N, f) != 7L * N) return 1; fclose(f);
    pl = malloc(4L * N * KK); int *lc = calloc(N, sizeof(int));
    for (int l = 0; l < NL; l++) for (int j = 0; j < KK; j++) { int p = lp[(size_t)l * KK + j]; pl[(size_t)p * KK + lc[p]++] = l; }
    for (int p = 0; p < N; p++) if (lc[p] != KK) { fprintf(stderr, "point %d on %d lines\n", p, lc[p]); return 1; }
    free(lc);
    wd = malloc(7L * N);
    for (int x = 0; x < N; x++) {
        const uint8_t *s = co + 7L * x; int8_t *w = wd + 7L * x;
        w[0] = s[4]; w[1] = s[5]; w[2] = s[6]; w[3] = (QQ - (2 * s[3]) % QQ) % QQ; w[4] = s[0]; w[5] = s[1]; w[6] = s[2];
    }
    cnt = calloc(N, sizeof(int32_t)); inS = calloc(N, 1); S = malloc(4L * N); spos = malloc(4L * N);
    bpos = malloc(4L * N); bcat = malloc(N); tabu_add = calloc(N, sizeof(int64_t)); tabu_rem = calloc(N, sizeof(int64_t));
    for (int x = 0; x < N; x++) { spos[x] = -1; bpos[x] = -1; bcat[x] = -1; }
    for (int c = 0; c <= LMAX; c++) { bk[c] = malloc(4L * N); bsz[c] = 0; }
    for (int x = 0; x < N; x++) bk_insert(x, 0);          /* all points start with cnt = 0 */

    rs ^= (uint64_t)atoll(argv[5]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 20; i++) rnd64();
    double secs = atof(argv[4]); double T = atof(argv[6]);

    if (strcmp(argv[2], "-") != 0) {
        FILE *g = fopen(argv[2], "r"); if (!g) return 1; char buf[256];
        while (fgets(buf, sizeof buf, g)) { int v; if (buf[0] == '#' || sscanf(buf, "%d", &v) != 1) continue;
            if (v < 0 || v >= N || inS[v]) { fprintf(stderr, "bad or repeated point %d\n", v); return 1; }
            addR(v); }
        fclose(g);
        fprintf(stderr, "initial file set: %d points, cost %lld\n", k, (long long)cost);
    }
    while (bsz[0] > 0 && cost == 0) addR(bk[0][rndint(bsz[0])]);   /* greedy fill with zero-conflict points */
    fprintf(stderr, "start: k = %d cost = %lld; bucket sizes cnt=0..%d:", k, (long long)cost, LMAX);
    for (int c = 0; c <= LMAX; c++) fprintf(stderr, " %d", bsz[c]);
    fprintf(stderr, "\n");

    int best_k = 0;
    if (cost == 0) { best_k = k; write_set(argv[3], "best"); }
    long iter = 0, acc = 0, improve = 0; double lastrep = 0;
    int tt_add = 10, tt_rem = 4;
    while (cpu() < secs) {
        iter++;
        if (cost == 0) {
            if (k > best_k) { best_k = k; write_set(argv[3], "best"); fprintf(stderr, "[%.1fs] it %ld: feasible k = %d\n", cpu(), iter, k); }
            if (bsz[0] > 0) { addR(bk[0][rndint(bsz[0])]); continue; }
            int c = 1; while (c <= LMAX && bsz[c] == 0) c++;
            if (c > LMAX) { fprintf(stderr, "no candidates\n"); break; }
            addR(bk[c][rndint(bsz[c])]);
            continue;
        }
        /* removal: tournament of two S points, prefer more conflicts */
        int y = -1;
        for (int t = 0; t < 4 && y < 0; t++) {
            int a = S[rndint(k)], b = S[rndint(k)];
            int cand = (cnt[a] >= cnt[b]) ? a : b;
            if (cnt[cand] > 0 && tabu_rem[cand] <= iter) y = cand;
        }
        if (y < 0) { for (int t = 0; t < 50 && y < 0; t++) { int a = S[rndint(k)]; if (tabu_rem[a] <= iter) y = a; } }
        if (y < 0) continue;
        /* addition: candidates from the two lowest nonempty buckets */
        int c0 = 0; while (c0 <= LMAX && bsz[c0] == 0) c0++;
        if (c0 > LMAX) continue;
        int bestx = -1, bestv = 1 << 30;
        for (int c = c0; c <= LMAX && c <= c0 + 1; c++) {
            int ns = bsz[c] < 24 ? bsz[c] : 24;
            for (int t = 0; t < ns; t++) {
                int x = bk[c][rndint(bsz[c])];
                if (tabu_add[x] > iter) continue;
                int v = cnt[x] - (Bxy(x, y) == 0);
                if (v < bestv || (v == bestv && rndint(2))) { bestv = v; bestx = x; }
            }
        }
        if (bestx < 0) continue;
        int64_t delta = (int64_t)bestv - cnt[y];
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            acc++;
            int xx = bestx;
            tabu_add[y] = iter + tt_add + rndint(tt_add);
            delR(y);
            addR(xx);
            tabu_rem[xx] = iter + tt_rem + rndint(tt_rem);
            if (delta < 0) improve++;
        }
        if (cpu() - lastrep > 20) {
            lastrep = cpu();
            fprintf(stderr, "[%.0fs] it %ld k=%d cost=%lld best_k=%d acc=%ld improve=%ld\n", cpu(), iter, k, (long long)cost, best_k, acc, improve);
        }
    }
    /* final consistency check */
    int64_t chk = 0;
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (Bxy(S[i], S[j]) == 0) chk++;
    fprintf(stderr, "done: iters %ld accepted %ld best_k %d final k %d cost %lld (check %lld)\n", iter, acc, best_k,
            k, (long long)cost, (long long)chk);
    printf("best %d\n", best_k);
    return 0;
}
