/* dpack.c: ILS for large "1-defective" partial distance-2 ovoids of H(q): point sets S (mode P; lines in mode L) in which
   every element of S is collinear (concurrent) with at most one other element of S, i.e. the collinearity graph induced
   on S is a matching.  Only elements with allow[e] = 1 may have a partner (a pair needs both ends allowed).  Used for the
   relaxed friendly surgery (research/d15D7b/RELAXED.md): a collinear pair {r, x} in a friendly set is repaired by hubs
   wired to freed elements incident with the partner, so pairing is allowed only where such freed elements exist.
   Moves: force-insert a random element (dropping the chosen elements that block it), refill the region greedily;
   best set kept, restored when the current falls behind.  Optional PAIRMAX caps the number of pairs.
   usage: dpack HEXBIN P|L SEED SECONDS START.txt ALLOW.txt|- PAIRMAX OUT.txt [FORBID.txt]   (ALLOW: ids allowed to pair; - = all)
   c6 variant: optional FORBID list of ids that are never added */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int q, N, Q1, *EC, *CE, *cnt, *sol, *pos, ns, npair, pairmax;
static char *in, *allow, *forb;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* nb(e): chosen elements collinear with e (excluding e) */
static int nbr(int e, int *who) {
    int k = 0;
    for (int i = 0; i < Q1; i++) { int c = EC[e * Q1 + i]; int cc = cnt[c] - (in[e] ? 1 : 0);
        if (cc > 0) for (int t = 0; t < Q1; t++) { int f = CE[c * Q1 + t]; if (f != e && in[f]) { if (who && k < 64) who[k] = f; k++; } } }
    return k;
}
static int partner(int e) { int w[64]; int k = nbr(e, w); return k ? w[0] : -1; }
static void add(int e) { in[e] = 1; pos[e] = ns; sol[ns++] = e; for (int i = 0; i < Q1; i++) cnt[EC[e * Q1 + i]]++; }
static void rem(int e) { in[e] = 0; int p = pos[e]; sol[p] = sol[--ns]; pos[sol[p]] = p; for (int i = 0; i < Q1; i++) cnt[EC[e * Q1 + i]]--; }
static int can_add(int e) {
    if (in[e] || forb[e]) return 0;
    int w[64]; int k = nbr(e, w);
    if (k == 0) return 1;
    if (k > 1 || !allow[e] || !allow[w[0]] || npair >= pairmax) return 0;
    return nbr(w[0], NULL) == 0;
}
static void add_chk(int e) { int w[64]; int k = nbr(e, w); add(e); if (k == 1) npair++; }
static void rem_chk(int e) { if (nbr(e, NULL) == 1) npair--; rem(e); }
static int cand[1 << 16];
static void refill(int *seeds, int nsd) {
    int nc = 0;
    for (int s = 0; s < nsd; s++) { int e = seeds[s];
        for (int i = 0; i < Q1; i++) { int c = EC[e * Q1 + i]; for (int t = 0; t < Q1; t++) if (nc < (1 << 16)) cand[nc++] = CE[c * Q1 + t]; } }
    for (int i = nc - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = cand[i]; cand[i] = cand[j]; cand[j] = t; }
    /* two passes: free elements first, then pairing ones */
    for (int i = 0; i < nc; i++) if (!in[cand[i]] && !forb[cand[i]] && nbr(cand[i], NULL) == 0) add_chk(cand[i]);
    for (int i = 0; i < nc; i++) if (can_add(cand[i])) add_chk(cand[i]);
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: dpack HEXBIN P|L SEED SECONDS START ALLOW|- PAIRMAX OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    int *LP = malloc(sizeof(int) * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    int *PL = malloc(sizeof(int) * N * Q1), *c0 = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int i = 0; i < Q1; i++) { int p = LP[l * Q1 + i]; PL[p * Q1 + c0[p]++] = l; }
    int modeL = argv[2][0] == 'L'; EC = modeL ? LP : PL; CE = modeL ? PL : LP;
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]); pairmax = atoi(argv[7]); if (pairmax <= 0) pairmax = 1 << 30;
    forb = calloc(N, 1); if (argc > 9) { FILE *h = fopen(argv[9], "r"); int e; while (fscanf(h, "%d", &e) == 1) forb[e] = 1; fclose(h); }
    cnt = calloc(N, sizeof(int)); in = calloc(N, 1); sol = malloc(sizeof(int) * N); pos = malloc(sizeof(int) * N); allow = malloc(N);
    if (strcmp(argv[6], "-") == 0) memset(allow, 1, N); else { memset(allow, 0, N); FILE *g = fopen(argv[6], "r"); int e; while (fscanf(g, "%d", &e) == 1) allow[e] = 1; fclose(g); }
    { FILE *g = fopen(argv[5], "r"); int e; while (fscanf(g, "%d", &e) == 1) { if (can_add(e)) add_chk(e); else fprintf(stderr, "start: skipped %d\n", e); } fclose(g); }
    int st0 = ns;
    int *perm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < N; i++) if (!in[perm[i]] && !forb[perm[i]] && nbr(perm[i], NULL) == 0) add_chk(perm[i]);
    for (int i = 0; i < N; i++) if (can_add(perm[i])) add_chk(perm[i]);
    fprintf(stderr, "start %d, greedy %d (pairs %d)\n", st0, ns, npair);
    int best = ns, bestp = npair; int *bs = malloc(sizeof(int) * N); memcpy(bs, sol, sizeof(int) * ns);
    double t0 = wall(); long it = 0; double lp = 0;
    int rm[256];
    while (1) {
        it++;
        if ((it & 255) == 0) { double el = wall() - t0; if (el > secs) break;
            if (el - lp > 60) { lp = el; fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d pairs=%d\n", el, it, ns, best, bestp);
                FILE *o = fopen(argv[8], "w"); for (int i = 0; i < best; i++) fprintf(o, "%d\n", bs[i]); fclose(o); } }
        int x; do { x = rnd() % N; } while (in[x] || forb[x]);
        int w[64]; int k = nbr(x, w); if (k > 6) continue;
        int nr = 0;
        /* drop blockers: all neighbours (and their partners' pair counts are handled by rem_chk) */
        for (int i = 0; i < k && i < 64; i++) if (in[w[i]]) { rem_chk(w[i]); rm[nr++] = w[i]; }
        add_chk(x);
        rm[nr++] = x;
        refill(rm, nr);
        if (ns > best) { best = ns; bestp = npair; memcpy(bs, sol, sizeof(int) * ns); }
        else if (ns < best - 2 || (ns < best && rnd() % 64 == 0)) {
            while (ns) { int e = sol[ns - 1]; rem(e); } npair = 0;
            for (int i = 0; i < best; i++) add_chk(bs[i]);
        }
    }
    /* verify */
    while (ns) rem(sol[ns - 1]); npair = 0;
    for (int i = 0; i < best; i++) add(bs[i]);
    int bad = 0, pr = 0;
    for (int i = 0; i < ns; i++) { int w[64]; int k = nbr(sol[i], w); if (k > 1) bad++; if (k == 1) { pr++; if (!allow[sol[i]]) bad++; if (nbr(w[0], NULL) != 1) bad++; } }
    FILE *o = fopen(argv[8], "w"); for (int i = 0; i < ns; i++) fprintf(o, "%d\n", sol[i]); fclose(o);
    printf("best %d (%d paired elements, %d pairs) after %ld iterations; violations %d\n", ns, pr, pr / 2, it, bad);
    return bad ? 2 : 0;
}
