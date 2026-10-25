/* ptls.c: card c4 (squad round 7). Point-level tabu / iterated local search for sets of pairwise-opposite points of H(13).
   Conflict graph: x ~ y iff B(x,y) = 0 mod 13 (non-opposite; distance <= 4 in the incidence graph).
   S is kept independent in this graph. conf[z] = number of members of S adjacent to z (z itself not counted),
   sumid[z] = sum of the indices of those members (for conf[z] = 1 this is the unique member).
   Buckets lv[k] hold the points outside S with conf = k (k <= KMAX): free points (k = 0) and 1-tight points (k = 1)
   are available without a scan.
   Each iteration: add a free non-tabu point (aspiration if it beats the best); else a (1,2)-swap (remove x, add two
   non-adjacent 1-tight points whose only member neighbour is x); else a plateau 1-swap (remove x, add a 1-tight
   non-tabu point, x tabu for a while); else perturbation (force in a non-tabu point of smallest conf >= 2, dropping
   its members into tabu). The best set is kept; after 20000 iterations without improvement the best is restored.
   Every add/remove is one scan of all N points: B(a,z) = a.z mod 13 with a = (x4, x5, x6, -2 x3, x0, x1, x2).
   usage: ptls HEXFILE SEEDFILE CPU_SECONDS RNGSEED OUTFILE   (OUTFILE gets the best set, one index per line) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define KMAX 40
static int N;
static uint8_t *co;
static int *conf, *sumid, *bkt, *lpos, *Sl, *Spos, *tabu, *lv[KMAX + 1];
static uint8_t *inS;
static int lvn[KMAX + 1], nS;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static inline void bk_del(int z) {
    int k = bkt[z];
    if (k < 0) return;
    int p = lpos[z], w = lv[k][--lvn[k]];
    lv[k][p] = w; lpos[w] = p; bkt[z] = -1;
}
static inline void bk_add(int z, int k) {
    if (k > KMAX) { bkt[z] = -1; return; }
    lv[k][lvn[k]] = z; lpos[z] = lvn[k]++; bkt[z] = k;
}
/* 1 iff B(x,y) = 0 mod 13 */
static inline int adj(int x, int y) {
    const uint8_t *a = co + 7L * x, *b = co + 7L * y;
    int s = a[4] * b[0] + a[5] * b[1] + a[6] * b[2] - 2 * a[3] * b[3] + a[0] * b[4] + a[1] * b[5] + a[2] * b[6];
    return s % 13 == 0;
}
static void scan_update(int x, int delta) {
    const uint8_t *ax = co + 7L * x;
    int c0 = ax[4], c1 = ax[5], c2 = ax[6], c3 = -2 * ax[3], c4 = ax[0], c5 = ax[1], c6 = ax[2];
    const uint8_t *p = co;
    for (int z = 0; z < N; z++, p += 7) {
        int s = c0 * p[0] + c1 * p[1] + c2 * p[2] + c3 * p[3] + c4 * p[4] + c5 * p[5] + c6 * p[6];
        if (s % 13 || z == x) continue;
        int nw = conf[z] + delta;
        conf[z] = nw; sumid[z] += delta * x;
        if (!inS[z]) { bk_del(z); bk_add(z, nw); }
    }
}
static void add_pt(int x) {            /* caller guarantees conf[x] == 0 */
    bk_del(x); inS[x] = 1; Spos[x] = nS; Sl[nS++] = x;
    scan_update(x, +1);
}
static void rem_pt(int x) {
    int p = Spos[x], w = Sl[--nS];
    Sl[p] = w; Spos[w] = p; inS[x] = 0;
    scan_update(x, -1);
    bk_add(x, conf[x]);
}
static double cpu_now(clock_t t0) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ptls HEXFILE SEEDFILE CPU_SECONDS RNGSEED OUTFILE\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    int32_t hdr[3];
    if (!f || fread(hdr, 4, 3, f) != 3) { fprintf(stderr, "cannot read hex header\n"); return 1; }
    int q = hdr[0], L = hdr[2];
    N = hdr[1];
    if (q != 13) { fprintf(stderr, "q must be 13\n"); return 1; }
    fseek(f, 12L + 4L * L * (q + 1), SEEK_SET);
    co = malloc(7L * N);
    if (fread(co, 1, 7L * N, f) != 7L * N) { fprintf(stderr, "short read\n"); return 1; }
    fclose(f);
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 2654435761ULL;
    for (int i = 0; i < 20; i++) rnd();
    conf = calloc(N, sizeof(int)); sumid = calloc(N, sizeof(int)); bkt = malloc(sizeof(int) * N);
    lpos = malloc(sizeof(int) * N); Sl = malloc(sizeof(int) * N); Spos = malloc(sizeof(int) * N);
    tabu = calloc(N, sizeof(int)); inS = calloc(N, 1);
    for (int k = 0; k <= KMAX; k++) lv[k] = malloc(sizeof(int) * N);
    for (int z = 0; z < N; z++) bkt[z] = -1;
    for (int z = 0; z < N; z++) bk_add(z, 0);
    nS = 0;
    FILE *g = fopen(argv[2], "r");
    if (!g) { fprintf(stderr, "no seed file\n"); return 1; }
    char buf[256]; int ns = 0, sk = 0, v;
    while (fgets(buf, sizeof buf, g)) {
        if (buf[0] == '#' || sscanf(buf, "%d", &v) != 1) continue;
        if (v < 0 || v >= N) continue;
        if (!inS[v] && conf[v] == 0) { add_pt(v); ns++; } else sk++;
    }
    fclose(g);
    fprintf(stderr, "N=%d L=%d seed loaded %d skipped %d |S|=%d buckets:", N, L, ns, sk, nS);
    for (int k = 0; k <= KMAX; k++) fprintf(stderr, " %d:%d", k, lvn[k]);
    fprintf(stderr, "\n");

    int best = nS;
    int *bestS = malloc(sizeof(int) * N);
    memcpy(bestS, Sl, sizeof(int) * nS);
    int *px = malloc(sizeof(int) * N), *pz = malloc(sizeof(int) * N), *nxt = malloc(sizeof(int) * N);
    int *mem = malloc(sizeof(int) * N), *ghead = malloc(sizeof(int) * N), *gstamp = calloc(N, sizeof(int));
    clock_t t0 = clock();
    long it = 0, lastImp = 0, nAdd = 0, n12 = 0, nSwap = 0, nPert = 0, nRestore = 0;
    while (1) {
        if ((it & 127) == 0 && cpu_now(t0) >= secs) break;
        it++;
        int I = (int)it;
        int tt = 7 + (int)(rnd() % 10);
        if (it - lastImp > 20000 && nS < best) {          /* restore the best set */
            while (nS) rem_pt(Sl[nS - 1]);
            for (int i = 0; i < best; i++) add_pt(bestS[i]);
            lastImp = it; nRestore++;
            continue;
        }
        /* (1) free add */
        if (lvn[0] > 0) {
            int n0 = lvn[0], off = (int)(rnd() % n0), cand = -1;
            for (int i = 0; i < n0; i++) {
                int z = lv[0][(off + i) % n0];
                if (tabu[z] <= I || nS + 1 > best) { cand = z; break; }
            }
            if (cand >= 0) {
                add_pt(cand); nAdd++;
                if (nS > best) { best = nS; memcpy(bestS, Sl, sizeof(int) * nS); lastImp = it;
                    fprintf(stderr, "it %ld cpu %.0f: new best %d\n", it, cpu_now(t0), best); }
                continue;
            }
        }
        /* (2) (1,2)-swap: group the non-tabu 1-tight points by their member neighbour x */
        int n1 = lvn[1], did = 0;
        if (n1 >= 2) {
            int m = 0, off = (int)(rnd() % n1);
            for (int i = 0; i < n1; i++) {
                int z = lv[1][(off + i) % n1];
                if (tabu[z] > I) continue;
                px[m] = sumid[z]; pz[m] = z; m++;
            }
            for (int i = 0; i < m; i++) {
                int x = px[i];
                if (gstamp[x] != I) { gstamp[x] = I; ghead[x] = -1; }
                nxt[i] = ghead[x]; ghead[x] = i;
            }
            for (int i = 0; i < m && !did; i++) {
                int x = px[i];
                if (gstamp[x] != I) continue;
                gstamp[x] = 0;
                int cnt = 0;
                for (int j = ghead[x]; j >= 0; j = nxt[j]) mem[cnt++] = pz[j];
                for (int a = 0; a < cnt && !did; a++)
                    for (int b = a + 1; b < cnt && !did; b++)
                        if (!adj(mem[a], mem[b])) {
                            rem_pt(x); tabu[x] = I + tt;
                            add_pt(mem[a]); add_pt(mem[b]);
                            n12++; did = 1;
                        }
            }
            if (did) {
                if (nS > best) { best = nS; memcpy(bestS, Sl, sizeof(int) * nS); lastImp = it;
                    fprintf(stderr, "it %ld cpu %.0f: new best %d\n", it, cpu_now(t0), best); }
                continue;
            }
        }
        /* (3) plateau 1-swap */
        if (n1 > 0) {
            int off = (int)(rnd() % n1), chosen = -1;
            for (int i = 0; i < n1; i++) {
                int z = lv[1][(off + i) % n1];
                if (tabu[z] <= I) { chosen = z; break; }
            }
            if (chosen >= 0) {
                int x = sumid[chosen];
                rem_pt(x); tabu[x] = I + tt;
                add_pt(chosen); nSwap++;
                continue;
            }
        }
        /* (4) perturbation: force in a non-tabu point of smallest conf >= 2, dropping its members */
        {
            int z = -1;
            for (int k = 2; k <= KMAX && z < 0; k++) {
                int nk = lvn[k];
                if (nk == 0) continue;
                int off = (int)(rnd() % nk);
                for (int i = 0; i < nk; i++) {
                    int c = lv[k][(off + i) % nk];
                    if (tabu[c] <= I) { z = c; break; }
                }
            }
            if (z < 0) { do { z = (int)(rnd() % N); } while (inS[z]); }
            for (int i = nS - 1; i >= 0; i--) {
                int y = Sl[i];
                if (adj(y, z)) { rem_pt(y); tabu[y] = I + tt; }
            }
            add_pt(z); nPert++;
        }
        if (it % 20000 == 0)
            fprintf(stderr, "it %ld cpu %.0f |S| %d best %d free %d one %d two %d | add %ld 12swap %ld swap %ld pert %ld restore %ld\n",
                    it, cpu_now(t0), nS, best, lvn[0], lvn[1], lvn[2], nAdd, n12, nSwap, nPert, nRestore);
    }
    int bad = 0;
    for (int i = 0; i < best; i++) for (int j = i + 1; j < best; j++) if (adj(bestS[i], bestS[j])) bad++;
    fprintf(stderr, "done: it=%ld best=%d internal adjacent pairs=%d adds=%ld 12swaps=%ld swaps=%ld perturb=%ld restores=%ld cpu=%.0f\n",
            it, best, bad, nAdd, n12, nSwap, nPert, nRestore, cpu_now(t0));
    FILE *o = fopen(argv[5], "w");
    if (!o) { fprintf(stderr, "cannot write output\n"); return 1; }
    fprintf(o, "# ptls best %d seed %s rng %s\n", best, argv[2], argv[4]);
    for (int i = 0; i < best; i++) fprintf(o, "%d\n", bestS[i]);
    fclose(o);
    printf("%d\n", best);
    return bad ? 1 : 0;
}
