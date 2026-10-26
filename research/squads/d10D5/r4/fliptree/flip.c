/* flip.c DEPTH SECS [TABFILE]: exact depth-bounded flip-tree search on nu (sigma, FD, coverage fixed).
 * A pair is bad iff it is unrouted and all its valid geodesics have equal nu-parity (unmixed).  Flipping a set T of
 * flags changes the bad count; score = bad count (coverage and D1 do not depend on nu).  DFS: pick a bad pair with the
 * fewest candidate flags (flags on some but not all of its valid geodesics, not already in T), branch on each.  Complete
 * for solutions of size <= DEPTH; every visited prefix is also scored, so the best partial flip set is reported.
 * Iterative deepening 1..DEPTH.  Prints best nbad, its flip set, nodes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define NF 3200
static int M, NU_N;
static int *flags;   /* M*32: flags[i*32 + g*4 + k] */
static unsigned char *vald;   /* M*8 */
static unsigned char *act;    /* M */
static int *inc_start, *inc_list; /* CSR: flag -> geo ids (i*8+g), valid & active only */
static unsigned char *par;    /* per geo */
static int *nv, *ones;        /* per pair */
static unsigned char *isbad;
static int *badlist, *badpos, nbad;
static unsigned char nu[NF], inT[NF];
static int T[64], bestT[64], bestN = 1 << 30, bestLen = 0;
static long long nodes = 0; static double t0, limit;
static int maxd;
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static inline void setbad(int i, int b) {
    if (b == isbad[i]) return;
    isbad[i] = b;
    if (b) { badpos[i] = nbad; badlist[nbad++] = i; }
    else { int p = badpos[i]; int j = badlist[--nbad]; badlist[p] = j; badpos[j] = p; badpos[i] = -1; }
}
static void flip(int f) {
    for (int e = inc_start[f]; e < inc_start[f + 1]; e++) {
        int geo = inc_list[e], i = geo >> 3;
        par[geo] ^= 1; ones[i] += par[geo] ? 1 : -1;
        int b = (ones[i] == 0 || ones[i] == nv[i]) && nv[i] > 0;
        setbad(i, b);
    }
    nu[f] ^= 1; inT[f] ^= 1;
}
/* candidates for pair i into out (distinct flags); returns count */
static int cands(int i, int *out) {
    int n = 0; int *fl = flags + i * 32;
    for (int a = 0; a < 32; a++) {
        int f = fl[a]; if (f < 0) continue;
        int g = a / 4; if (!vald[i * 8 + g]) continue;
        if (inT[f]) continue;
        int dup = 0; for (int b = 0; b < n; b++) if (out[b] == f) { dup = 1; break; }
        if (dup) continue;
        /* count valid geodesics containing f (distinct) */
        int cnt = 0;
        for (int h = 0; h < 8; h++) {
            if (!vald[i * 8 + h]) continue;
            int has = 0; for (int k = 0; k < 4; k++) if (fl[h * 4 + k] == f) has = 1;
            cnt += has;
        }
        if (cnt > 0 && cnt < nv[i]) out[n++] = f;
    }
    return n;
}
static int bestcands_pair(int *outbuf, int *outn) {
    /* choose bad pair with fewest candidates; fill outbuf */
    int bi = -1, bn = 1 << 30; static int tmp[32];
    for (int b = 0; b < nbad; b++) {
        int i = badlist[b]; int n = cands(i, tmp);
        if (n < bn) { bn = n; bi = i; memcpy(outbuf, tmp, sizeof(int) * n); if (bn == 0) break; }
    }
    *outn = bn; return bi;
}
static int found = 0;
static void record(int depth) {
    if (nbad < bestN) {
        bestN = nbad; bestLen = depth; memcpy(bestT, T, sizeof(int) * depth);
        printf("best nbad=%d depth=%d nodes=%lld t=%.1fs\n", bestN, depth, nodes, now() - t0); fflush(stdout);
    }
}
static int hitc[NF];
static int prune_on = 1;
static int dfs(int depth) {
    nodes++;
    if ((nodes & 0xFFFFF) == 0 && now() - t0 > limit) return -1;
    record(depth);
    if (nbad == 0) return 1;
    if (depth == maxd) return 0;
    int r = maxd - depth;
    if (nbad > 256) return 0;
    static __thread int cb[256][32]; int cn[256];
    int touched[256 * 32], nt = 0, bi = -1, bn = 1 << 30;
    for (int b = 0; b < nbad; b++) {
        int i = badlist[b]; cn[b] = cands(i, cb[b]);
        if (cn[b] < bn) { bn = cn[b]; bi = b; }
        for (int a = 0; a < cn[b]; a++) { int f = cb[b][a]; if (hitc[f] == 0) touched[nt++] = f; hitc[f]++; }
    }
    int maxh = 0;
    for (int t = 0; t < nt; t++) if (hitc[touched[t]] > maxh) maxh = hitc[touched[t]];
    for (int t = 0; t < nt; t++) hitc[touched[t]] = 0;
    /* hitting-set bound: remaining r flips must each hit at most maxh of the nbad bad pairs */
    if (prune_on && (long)nbad > (long)r * maxh) return 0;
    int own[32]; int on = cn[bi]; memcpy(own, cb[bi], sizeof(int) * on);
    for (int a = 0; a < on; a++) {
        int f = own[a];
        flip(f); T[depth] = f;
        int rr = dfs(depth + 1);
        if (rr) { if (rr == 1) return 1; flip(f); return rr; }
        flip(f);
    }
    return 0;
}
int main(int argc, char **argv) {
    int DEPTH = argc > 1 ? atoi(argv[1]) : 3; limit = argc > 2 ? atof(argv[2]) : 60;
    const char *tf = argc > 3 ? argv[3] : "tab.bin";
    FILE *fp = fopen(tf, "rb"); if (!fp) { perror("tab"); return 1; }
    int hdr[2]; fread(hdr, 4, 2, fp); M = hdr[0]; NU_N = hdr[1];
    int *rec = malloc(sizeof(int) * 41 * (size_t)M);
    fread(rec, 4, 41 * (size_t)M, fp);
    int nunu[NF]; fread(nunu, 4, NF, fp); fclose(fp);
    flags = malloc(sizeof(int) * 32 * (size_t)M); vald = malloc(8 * (size_t)M); act = malloc(M);
    for (int i = 0; i < M; i++) {
        int *r = rec + 41 * (size_t)i;
        memcpy(flags + 32 * (size_t)i, r, 32 * sizeof(int));
        for (int g = 0; g < 8; g++) vald[i * 8 + g] = (unsigned char)r[32 + g];
        act[i] = (unsigned char)r[40];
    }
    free(rec);
    for (int f = 0; f < NF; f++) nu[f] = (unsigned char)nunu[f];
    /* incidence CSR over valid geodesics of active pairs */
    int *cnt = calloc(NF + 1, sizeof(int));
    for (int i = 0; i < M; i++) if (act[i]) for (int g = 0; g < 8; g++) if (vald[i * 8 + g])
        for (int k = 0; k < 4; k++) cnt[flags[i * 32 + g * 4 + k] + 1]++;
    inc_start = malloc(sizeof(int) * (NF + 1)); inc_start[0] = 0;
    for (int f = 0; f < NF; f++) inc_start[f + 1] = inc_start[f] + cnt[f + 1];
    int tot = inc_start[NF]; inc_list = malloc(sizeof(int) * (tot + 1));
    int *fillp = malloc(sizeof(int) * NF); memcpy(fillp, inc_start, sizeof(int) * NF);
    par = calloc(M * 8, 1); nv = calloc(M, sizeof(int)); ones = calloc(M, sizeof(int));
    isbad = calloc(M, 1); badlist = malloc(sizeof(int) * (M + 1)); badpos = malloc(sizeof(int) * M);
    for (int i = 0; i < M; i++) {
        badpos[i] = -1;
        if (!act[i]) continue;
        for (int g = 0; g < 8; g++) if (vald[i * 8 + g]) {
            int p = 0; nv[i]++;
            for (int k = 0; k < 4; k++) { int f = flags[i * 32 + g * 4 + k]; p ^= nu[f]; inc_list[fillp[f]++] = i * 8 + g; }
            par[i * 8 + g] = p; ones[i] += p;
        }
    }
    for (int i = 0; i < M; i++) if (act[i]) {
        int b = (ones[i] == 0 || ones[i] == nv[i]) && nv[i] > 0; setbad(i, b);
    }
    /* per-flag incidence list is built from geodesic flags with multiplicity; fine for parity */
    printf("M=%d start nbad=%d\n", M, nbad); fflush(stdout);
    if (nbad == 0) { printf("already zero\n"); return 0; }
    t0 = now(); bestN = nbad; bestLen = 0;
    for (maxd = 1; maxd <= DEPTH; maxd++) {
        int r = dfs(0);
        printf("depth %d done: r=%d nodes=%lld best=%d t=%.1fs\n", maxd, r, nodes, bestN, now() - t0); fflush(stdout);
        if (r == 1) { printf("FOUND zero, flips:"); for (int j = 0; j < maxd; j++) { int x = T[j]; printf(" %d", x); } printf("\n"); break; }
        if (r == -1) break;
    }
    printf("BEST %d FLIPS", bestN); for (int j = 0; j < bestLen; j++) printf(" %d", bestT[j]); printf("\n");
    return 0;
}
