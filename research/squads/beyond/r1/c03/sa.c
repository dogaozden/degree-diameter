/* Max set packing for the (q+2,4) shadow-line problem on Q(4,q).
   Lines L (q+1 points). Capacity: non-ovoid point 1, ovoid point 2. Maximize #lines chosen.
   Penalty E = sum_p max(0, cnt_p - cap_p); k-fixed simulated annealing, grow k when E==0.
   usage: ./sa INST SECONDS SEED T OUT   (writes best selection as: k then line indices, on every improvement) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>
#include <stdint.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int N, M, NO, L1; /* L1 = q+1 */
int *lp;          /* M x L1 */
int *cap, *cnt;
int *onl;         /* points -> lines: N x (q+1) */
int *sel, *selpos, *selist; int k;
int *uns, *unpos; int nu;
int E;

static void add_line(int b, int dir) { /* dir=+1 select, -1 deselect */
    (void)b; (void)dir;
}

static int addpen(int b) { int s = 0; for (int i = 0; i < L1; i++) { int p = lp[b * L1 + i]; if (cnt[p] >= cap[p]) s++; } return s; }

static void select_line(int b) {
    for (int i = 0; i < L1; i++) { int p = lp[b * L1 + i]; if (cnt[p] >= cap[p]) E++; cnt[p]++; }
    sel[b] = 1; selpos[b] = k; selist[k++] = b;
    int u = unpos[b]; int last = uns[--nu]; uns[u] = last; unpos[last] = u;
}
static void deselect_line(int a) {
    for (int i = 0; i < L1; i++) { int p = lp[a * L1 + i]; cnt[p]--; if (cnt[p] >= cap[p]) E--; }
    sel[a] = 0; int pos = selpos[a]; int last = selist[--k]; selist[pos] = last; selpos[last] = pos;
    unpos[a] = nu; uns[nu++] = a;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    double secs = atof(argv[2]); rs = strtoull(argv[3], 0, 10) * 2654435761ULL + 88172645463325252ULL; double T = atof(argv[4]);
    const char *outf = argv[5];
    if (fscanf(f, "%d %d %d", &N, &M, &NO) != 3) return 2;
    int q = 0; /* infer L1 from first line length */
    /* read ovoid */
    cap = malloc(N * sizeof(int)); cnt = calloc(N, sizeof(int));
    for (int i = 0; i < N; i++) cap[i] = 1;
    for (int i = 0; i < NO; i++) { int o; if (fscanf(f, "%d", &o) != 1) return 3; cap[o] = 2; }
    lp = malloc((size_t)M * 64 * sizeof(int)); /* q+1 <= 64 */
    L1 = 0;
    /* lines: q+1 numbers each; q+1 = (N / (q^2+1)) ... derive from NO: NO = q^2+1 */
    q = (int)llround(sqrt(NO - 1)); L1 = q + 1;
    lp = realloc(lp, (size_t)M * L1 * sizeof(int));
    for (int j = 0; j < M; j++) for (int i = 0; i < L1; i++) if (fscanf(f, "%d", &lp[j * L1 + i]) != 1) return 4;
    fclose(f);
    onl = malloc((size_t)N * (q + 1) * sizeof(int)); int *dg = calloc(N, sizeof(int));
    for (int j = 0; j < M; j++) for (int i = 0; i < L1; i++) { int p = lp[j * L1 + i]; onl[p * (q + 1) + dg[p]++] = j; }
    sel = calloc(M, sizeof(int)); selpos = calloc(M, sizeof(int)); selist = malloc(M * sizeof(int));
    uns = malloc(M * sizeof(int)); unpos = malloc(M * sizeof(int));
    nu = 0; for (int j = 0; j < M; j++) { unpos[j] = nu; uns[nu++] = j; }
    k = 0; E = 0;
    int best = 0; clock_t t0 = clock();
    /* grow greedily to start */
    while (k < 1) { int bb = -1, bp = 1 << 30; for (int t = 0; t < 2000; t++) { int b = uns[rnd() % nu]; int pen = addpen(b); if (pen < bp) { bp = pen; bb = b; } } select_line(bb); }
    long long it = 0; int *tmp = malloc(M * sizeof(int));
    while (1) {
        if ((it & 0xFFFF) == 0) { double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break; }
        it++;
        if (E == 0) {
            if (k > best) {
                best = k;
                FILE *g = fopen(outf, "w"); fprintf(g, "%d\n", k); for (int i = 0; i < k; i++) fprintf(g, "%d\n", selist[i]); fclose(g);
                printf("best %d at %.1fs it=%lld\n", best, (double)(clock() - t0) / CLOCKS_PER_SEC, it); fflush(stdout);
            }
            /* add the least-penalty unselected line (sampled) */
            int bb = -1, bp = 1 << 30;
            for (int t = 0; t < 4000; t++) { int b = uns[rnd() % nu]; int pen = addpen(b); if (pen < bp || (pen == bp && (rnd() & 1))) { bp = pen; bb = b; } }
            select_line(bb);
            continue;
        }
        /* pick a selected line touching a violated point (sample) */
        int a = -1;
        for (int t = 0; t < 64; t++) {
            int c = selist[rnd() % k]; int bad = 0;
            for (int i = 0; i < L1; i++) { int p = lp[c * L1 + i]; if (cnt[p] > cap[p]) { bad = 1; break; } }
            if (bad) { a = c; break; }
        }
        if (a < 0) a = selist[rnd() % k];
        /* pick an unselected line with small addition penalty (best of 6 samples) */
        int b = -1, bp = 1 << 30;
        for (int t = 0; t < 6; t++) { int c = uns[rnd() % nu]; int pen = addpen(c); if (pen < bp) { bp = pen; b = c; } }
        int E0 = E;
        deselect_line(a);
        select_line(b);
        int dE = E - E0;
        if (dE <= 0 || urand() < exp(-dE / T)) {
            /* accept */
        } else {
            deselect_line(b);
            select_line(a);
        }
    }
    printf("done best=%d it=%lld E=%d k=%d\n", best, it, E, k);
    return 0;
}
