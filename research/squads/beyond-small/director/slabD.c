/* slabC: fibre-level slab design (supersedes slabB). slabB: step B of the slab design (director, job beyond-small). One side at a time.
 * Input: slabA's per-fibre directions (c, z, z'). Scaffold: PG(2, K-1) with K = 4 (13 points, 13 lines), COPIES
 * connectors per line (connector index = copy*13 + line, i.e. line = index % 13 as in scaffold.c), 12 hubs per connector.
 *   1. Domination: each line l gets a set F_l of T-fibres; at each fibre in F_l one hyperplane (coset of span(c,z,z'))
 *      is reserved for l and its 4 slabs go one to each copy of l. For every root R, the union of F_l over the lines
 *      through R must dominate the S-controller (every S-fibre has a controller neighbour in it); a hyperplane at
 *      fibre f dominates all S-fibres adjacent to f (checked in step A).
 *   2. Coverage: each connector gets 12 slabs at distinct fibres (its hyperplane slabs + free slabs) whose slab-D2 sets
 *      cover every T-fibre completely (greedy on the exact full-fibre lists).
 *   3. Hubs: the connector's 48 lines are split into 12 quadruples, each covering S within distance 3.
 * Output: hub pool file in connector order (12 hubs per connector, 16 global ids per line), usable by scaffold.c.
 * usage: slabB EDGES SIDE SLABA_FILE COPIES NDOM SEED OUT */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define H 16896
#define W 264
static int MINCOV = 63;
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static int (*adjT)[16], (*adjS)[16];
static uint64_t *d2, *ball;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static int K = 4, npts, lines[64][8];
static void make_plane(int q) {
    int add[8][8], mul[8][8];
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        if (q == 4) { add[a][b] = a ^ b; mul[a][b] = MUL4[a][b]; } else { add[a][b] = (a + b) % q; mul[a][b] = a * b % q; } }
    int P[64][3]; npts = 0;
    for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) { P[npts][0] = 1; P[npts][1] = x; P[npts][2] = y; npts++; }
    for (int y = 0; y < q; y++) { P[npts][0] = 0; P[npts][1] = 1; P[npts][2] = y; npts++; }
    P[npts][0] = 0; P[npts][1] = 0; P[npts][2] = 1; npts++;
    for (int l = 0; l < npts; l++) { int c = 0;
        for (int p = 0; p < npts; p++) { int s = 0; for (int k = 0; k < 3; k++) s = add[s][mul[P[l][k]][P[p][k]]]; if (s == 0) lines[l][c++] = p; } }
}
static int fc[66], fz[66], fz2[66];
static int slabid[66][256], hypid[66][256], lineid[66][256], lineid5[66][5][256], dir5[66][5];   /* coset ids within the fibre */
static int slab_of_hyp[66][4][4];                              /* hyperplane h at fibre f -> its 4 slab ids */
static int slabpts[66][16][16];                                /* slab -> 16 point offsets */
static uint64_t slabD2[66][16][2];                             /* full T-fibres covered by D2(slab), as a 66-bit set */
static uint64_t ctrlN[66][2];                                  /* S-fibres adjacent to T-fibre f */

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: slabB EDGES SIDE SLABA COPIES NDOM SEED OUT\n"); return 2; }
    int side = atoi(argv[2]), COP = atoi(argv[4]), NDOM = atoi(argv[5]); rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    adjT = side == 0 ? adjB : adjA; adjS = side == 0 ? adjA : adjB;
    d2 = calloc((size_t)H * W, 8); ball = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) { uint64_t *dd = d2 + (size_t)t * W, *bl = ball + (size_t)t * W; dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjT[t][i]; bl[s >> 6] |= 1ULL << (s & 63); for (int j = 0; j < 16; j++) { int t2 = adjS[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b; for (int i = 0; i < 16; i++) { int s = adjT[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } } }
    make_plane(K - 1);
    f = fopen(argv[3], "r");
    for (int i = 0; i < 66; i++) { int fb, a, b, c2, x1, x2, x3; if (fscanf(f, "%d %d %d %d %d %d %d", &fb, &a, &b, &c2, &x1, &x2, &x3) != 7) return 4; fc[fb] = a; fz[fb] = b; fz2[fb] = c2; }
    fclose(f);
    /* cosets */
    for (int fb = 0; fb < 66; fb++) {
        int L[4], S[16], P[64];
        for (int l = 0; l < 4; l++) L[l] = scal(l, fc[fb]);
        for (int l = 0; l < 4; l++) for (int m = 0; m < 4; m++) S[l * 4 + m] = scal(l, fc[fb]) ^ scal(m, fz[fb]);
        for (int i = 0; i < 16; i++) for (int l = 0; l < 4; l++) P[i * 4 + l] = S[i] ^ scal(l, fz2[fb]);
        dir5[fb][0] = fc[fb]; dir5[fb][1] = fz[fb]; dir5[fb][2] = fc[fb] ^ fz[fb]; dir5[fb][3] = fc[fb] ^ scal(2, fz[fb]); dir5[fb][4] = fc[fb] ^ scal(3, fz[fb]);
        for (int d = 0; d < 5; d++) { int sn[256]; memset(sn, -1, sizeof sn); int k = 0; for (int y = 0; y < 256; y++) if (sn[y] < 0) { for (int l = 0; l < 4; l++) sn[y ^ scal(l, dir5[fb][d])] = k; k++; } memcpy(lineid5[fb][d], sn, sizeof sn); }
        int ns = 0, nh = 0, nl = 0, seen[256];
        memset(seen, -1, sizeof seen); for (int y = 0; y < 256; y++) if (seen[y] < 0) { for (int i = 0; i < 4; i++) seen[y ^ L[i]] = nl; nl++; } memcpy(lineid[fb], seen, sizeof seen);
        memset(seen, -1, sizeof seen); for (int y = 0; y < 256; y++) if (seen[y] < 0) { for (int i = 0; i < 16; i++) { seen[y ^ S[i]] = ns; slabpts[fb][ns][i] = y ^ S[i]; } ns++; } memcpy(slabid[fb], seen, sizeof seen);
        memset(seen, -1, sizeof seen); for (int y = 0; y < 256; y++) if (seen[y] < 0) { for (int i = 0; i < 64; i++) seen[y ^ P[i]] = nh; nh++; } memcpy(hypid[fb], seen, sizeof seen);
        if (ns != 16 || nh != 4 || nl != 64) { fprintf(stderr, "fibre %d: bad directions\n", fb); return 5; }
        int cnt[4] = {0}; for (int s = 0; s < 16; s++) { int h = hypid[fb][slabpts[fb][s][0]]; slab_of_hyp[fb][h][cnt[h]++] = s; }
        for (int s = 0; s < 16; s++) { uint64_t acc[W]; memset(acc, 0, sizeof acc);
            for (int i = 0; i < 16; i++) { uint64_t *dd = d2 + (size_t)(fb * 256 + slabpts[fb][s][i]) * W; for (int w = 0; w < W; w++) acc[w] |= dd[w]; }
            slabD2[fb][s][0] = slabD2[fb][s][1] = 0;
            for (int g = 0; g < 66; g++) { int ok = 1; for (int w = g * 4; w < g * 4 + 4; w++) if (acc[w] != ~0ULL) ok = 0; if (ok) slabD2[fb][s][g >> 6] |= 1ULL << (g & 63); } }
        ctrlN[fb][0] = ctrlN[fb][1] = 0;
        for (int y = 0; y < 256; y++) for (int k = 0; k < 16; k++) { int s = adjT[fb * 256 + y][k] / 256; ctrlN[fb][s >> 6] |= 1ULL << (s & 63); }
    }
    /* covering quadruples of fibres (offset-independent; representative line = line of offset 0) */
    int TD = getenv("TD") ? atoi(getenv("TD")) : 2;      /* line directions kept per fibre */
    uint64_t (*FB)[W] = malloc(sizeof(uint64_t[W]) * 66 * 5); int topd[66][5];
    for (int fb = 0; fb < 66; fb++) { int sc[5];
        for (int d = 0; d < 5; d++) { uint64_t *o = FB[fb * 5 + d]; memset(o, 0, sizeof(uint64_t) * W);
            for (int y = 0; y < 256; y++) if (lineid5[fb][d][y] == lineid5[fb][d][0]) { uint64_t *bl = ball + (size_t)(fb * 256 + y) * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; }
            sc[d] = popw(o); }
        for (int k = 0; k < 5; k++) { int bi = 0; for (int d = 1; d < 5; d++) if (sc[d] > sc[bi]) bi = d; topd[fb][k] = bi; sc[bi] = -1; } }
    int (*Q)[4] = malloc(sizeof(int[4]) * 4000000); int nq = 0;     /* element = fibre*5 + dir */
    for (int a = 0; a < 66; a++) for (int b = a + 1; b < 66; b++) for (int da2 = 0; da2 < TD; da2++) for (int db2 = 0; db2 < TD; db2++) {
        int ea = a * 5 + topd[a][da2], eb = b * 5 + topd[b][db2]; uint64_t ab[W]; for (int w = 0; w < W; w++) ab[w] = FB[ea][w] | FB[eb][w];
        for (int c = b + 1; c < 66; c++) for (int dc = 0; dc < TD; dc++) { int ec = c * 5 + topd[c][dc]; uint64_t abc[W]; for (int w = 0; w < W; w++) abc[w] = ab[w] | FB[ec][w];
            for (int d = c + 1; d < 66; d++) for (int dd = 0; dd < TD; dd++) { int ed = d * 5 + topd[d][dd]; int ok = 1; for (int w = 0; w < W && ok; w++) if ((abc[w] | FB[ed][w]) != ~0ULL) ok = 0;
                if (ok && nq < 4000000) { Q[nq][0] = ea; Q[nq][1] = eb; Q[nq][2] = ec; Q[nq][3] = ed; nq++; } } } }
    printf("covering quadruples: %d of %d\n", nq, 720720);
    /* N2 sets (intersection over the 16 slabs of a fibre, to be offset-safe) */
    uint64_t N2[66][2]; for (int fb = 0; fb < 66; fb++) { N2[fb][0] = N2[fb][1] = ~0ULL; for (int s2 = 0; s2 < 16; s2++) { N2[fb][0] &= slabD2[fb][s2][0]; N2[fb][1] &= slabD2[fb][s2][1]; } }
    uint64_t ALL0 = ~0ULL, ALL1 = (1ULL << 2) - 1;
    { int nd = 0, best = 0; long tot = 0; int fibreuse[66] = {0};
      for (int i = 0; i < nq; i++) for (int k = 0; k < 4; k++) fibreuse[Q[i][k] / 5]++;
      int nf = 0; for (int fb = 0; fb < 66; fb++) nf += fibreuse[fb] > 0;
      for (int t = 0; t < 100000; t++) { int q1 = rnd() % nq, q2 = rnd() % nq, q3 = rnd() % nq; int fs[12]; memcpy(fs, Q[q1], 16); memcpy(fs + 4, Q[q2], 16); memcpy(fs + 8, Q[q3], 16); for (int i = 0; i < 12; i++) fs[i] /= 5;
        int bad = 0; for (int i = 0; i < 12 && !bad; i++) for (int j = i + 1; j < 12; j++) if (fs[i] == fs[j]) bad = 1; if (bad) continue; nd++;
        uint64_t c0 = 0, c1 = 0; for (int i = 0; i < 12; i++) { c0 |= N2[fs[i]][0]; c1 |= N2[fs[i]][1]; }
        int c = __builtin_popcountll(c0) + __builtin_popcountll(c1 & ALL1); tot += c; if (c > best) best = c; }
      int n2min = 99; for (int fb = 0; fb < 66; fb++) { int c = __builtin_popcountll(N2[fb][0]) + __builtin_popcountll(N2[fb][1] & ALL1); if (c < n2min) n2min = c; }
      printf("diag: %d fibres appear in covering quadruples; disjoint triples %d of 100000, D2 coverage mean %.1f max %d of 66; min |N2(f)| %d\n", nf, nd, nd ? (double)tot / nd : 0, best, n2min); }
    int (*GT)[3] = malloc(sizeof(int[3]) * 2000000); int ngt = 0; int hist[67] = {0};
    for (int i = 0; i < nq; i++) for (int j = i + 1; j < nq; j++) {
        int dis = 1; for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) if (Q[i][a] / 5 == Q[j][b] / 5) dis = 0; if (!dis) continue;
        uint64_t ij0 = 0, ij1 = 0; for (int a = 0; a < 4; a++) { ij0 |= N2[Q[i][a] / 5][0] | N2[Q[j][a] / 5][0]; ij1 |= N2[Q[i][a] / 5][1] | N2[Q[j][a] / 5][1]; }
        for (int k = j + 1; k < nq; k++) {
            int d2 = 1; for (int a = 0; a < 4 && d2; a++) for (int b = 0; b < 4; b++) if (Q[k][a] / 5 == Q[i][b] / 5 || Q[k][a] / 5 == Q[j][b] / 5) d2 = 0; if (!d2) continue;
            uint64_t c0 = ij0, c1 = ij1; for (int a = 0; a < 4; a++) { c0 |= N2[Q[k][a] / 5][0]; c1 |= N2[Q[k][a] / 5][1]; }
            int c = __builtin_popcountll(c0) + __builtin_popcountll(c1 & ALL1); hist[c]++;
            if (c >= MINCOV && ngt < 2000000) { GT[ngt][0] = i; GT[ngt][1] = j; GT[ngt][2] = k; ngt++; } } }
    printf("good triples (full D2 coverage): %d; coverage histogram 60..66:", ngt); for (int c = 60; c <= 66; c++) printf(" %d", hist[c]); printf("\n");
    /* search the 13 fibre sets */
    int Phi[64][3], cap[66]; int found = 0, bestw = -1, bestPhi[64][3];
    for (int att = 0; att < (getenv("ATT") ? atoi(getenv("ATT")) : 20000) && !found; att++) {
        memset(cap, 0, sizeof cap); int okall = 1;
        for (int l = 0; l < npts && okall; l++) {
            int done = 0;
            for (int t = 0; t < 4000 && !done; t++) {
                if (ngt == 0) break; int gi = rnd() % ngt; int q1 = GT[gi][0], q2 = GT[gi][1], q3 = GT[gi][2]; int fs[12]; memcpy(fs, Q[q1], 16); memcpy(fs + 4, Q[q2], 16); memcpy(fs + 8, Q[q3], 16); for (int i = 0; i < 12; i++) fs[i] /= 5;
                int bad = 0; for (int i = 0; i < 12 && !bad; i++) { if (cap[fs[i]] >= 4) bad = 1; for (int j = i + 1; j < 12; j++) if (fs[i] == fs[j]) bad = 1; }
                if (bad) continue;
                uint64_t c0 = 0, c1 = 0; for (int i = 0; i < 12; i++) { c0 |= N2[fs[i]][0]; c1 |= N2[fs[i]][1]; }
                if (__builtin_popcountll(c0) + __builtin_popcountll(c1 & ALL1) < MINCOV) continue;
                Phi[l][0] = q1; Phi[l][1] = q2; Phi[l][2] = q3; for (int i = 0; i < 12; i++) cap[fs[i]]++; done = 1;
            }
            if (!done) okall = 0;
        }
        if (!okall) continue;
        /* root domination */
        int worst = 99;
        for (int R = 0; R < npts; R++) { uint64_t cv0 = 0, cv1 = 0;
            for (int m = 0; m < npts; m++) { int on = 0; for (int kk = 0; kk < K; kk++) if (lines[m][kk] == R) on = 1; if (!on) continue;
                for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) { int fb = Q[Phi[m][qq]][i] / 5; cv0 |= ctrlN[fb][0]; cv1 |= ctrlN[fb][1]; } }
            int c = __builtin_popcountll(cv0) + __builtin_popcountll(cv1 & ALL1); if (c < worst) worst = c; }
        if (worst > bestw) { bestw = worst; memcpy(bestPhi, Phi, sizeof Phi); }
        if (worst == 66) found = 1;
        if (att % 1000 == 0) printf("attempt %d worst root %d\n", att, worst);
    }
    if (bestw < 0) { printf("no design found\n"); return 7; }
    memcpy(Phi, bestPhi, sizeof Phi);
    /* local search: replace one line's triple, objective = 1000 * sum of undominated (root, S-fibre) + sum of uncovered (line, T-fibre) */
    {
        #define TRI(l) Q[Phi[l][0]], Q[Phi[l][1]], Q[Phi[l][2]]
        int capn[66]; memset(capn, 0, sizeof capn);
        for (int l = 0; l < npts; l++) for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) capn[Q[Phi[l][qq]][i] / 5]++;
        long obj = 0;
        #define OBJ(res) do { long _o = 0; \
            for (int R = 0; R < npts; R++) { uint64_t cv0 = 0, cv1 = 0; \
                for (int m = 0; m < npts; m++) { int on = 0; for (int kk = 0; kk < K; kk++) if (lines[m][kk] == R) on = 1; if (!on) continue; \
                    for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) { int fb = Q[Phi[m][qq]][i] / 5; cv0 |= ctrlN[fb][0]; cv1 |= ctrlN[fb][1]; } } \
                _o += 1000L * (66 - __builtin_popcountll(cv0) - __builtin_popcountll(cv1 & ALL1)); } \
            for (int m = 0; m < npts; m++) { uint64_t c0 = 0, c1 = 0; for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) { c0 |= N2[Q[Phi[m][qq]][i] / 5][0]; c1 |= N2[Q[Phi[m][qq]][i] / 5][1]; } \
                for (int fb = 0; fb < 66; fb++) if (!(((fb < 64 ? c0 : c1) >> (fb & 63)) & 1) && capn[fb] < 4) _o++; } \
            res = _o; } while (0)
        OBJ(obj);
        printf("local search start objective %ld\n", obj);
        long iters = getenv("LSIT") ? atol(getenv("LSIT")) : 200000;
        for (long it = 0; it < iters && obj > 0; it++) {
            int l = rnd() % npts, gi = rnd() % ngt; int old[3] = {Phi[l][0], Phi[l][1], Phi[l][2]};
            int ok = 1; for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) capn[Q[old[qq]][i] / 5]--;
            for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) if (capn[Q[GT[gi][qq]][i] / 5] >= 4) ok = 0;
            if (ok) { for (int qq = 0; qq < 3; qq++) { Phi[l][qq] = GT[gi][qq]; for (int i = 0; i < 4; i++) capn[Q[GT[gi][qq]][i] / 5]++; }
                long o2; OBJ(o2);
                if (o2 <= obj) obj = o2; else { for (int qq = 0; qq < 3; qq++) { for (int i = 0; i < 4; i++) capn[Q[Phi[l][qq]][i] / 5]--; Phi[l][qq] = old[qq]; for (int i = 0; i < 4; i++) capn[Q[old[qq]][i] / 5]++; } } }
            else for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) capn[Q[old[qq]][i] / 5]++;
        }
        printf("local search end objective %ld (domination misses %ld, coverage misses %ld)\n", obj, obj / 1000, obj % 1000);
    }

    printf("design: worst root dominates %d of 66 (sufficient condition)\n", bestw);
    if (getenv("DUMP")) {   /* data for scafopt: quadruples, good triples, slab lines for every (fibre, hyperplane, copy, direction), start Phi */
        FILE *dmp = fopen(getenv("DUMP"), "wb");
        fwrite(&nq, 4, 1, dmp); fwrite(Q, sizeof(int[4]), nq, dmp); fwrite(&ngt, 4, 1, dmp); fwrite(GT, sizeof(int[3]), ngt, dmp);
        static int L4[66][4][4][5][4][4];
        for (int fb = 0; fb < 66; fb++) for (int h = 0; h < 4; h++) for (int j = 0; j < 4; j++) for (int d = 0; d < 5; d++) {
            int s2 = slab_of_hyp[fb][h][j]; int lids[4], nlid = 0;
            for (int k = 0; k < 16; k++) { int li = lineid5[fb][d][slabpts[fb][s2][k]]; int seen = 0; for (int t = 0; t < nlid; t++) if (lids[t] == li) seen = 1; if (!seen) lids[nlid++] = li; }
            for (int a = 0; a < 4; a++) { int m = 0; for (int k = 0; k < 16; k++) if (lineid5[fb][d][slabpts[fb][s2][k]] == lids[a]) L4[fb][h][j][d][a][m++] = fb * 256 + slabpts[fb][s2][k] + (side == 0 ? H : 0); } }
        fwrite(L4, sizeof L4, 1, dmp); fwrite(Phi, sizeof(int[3]), npts, dmp); fclose(dmp);
        printf("dumped design data to %s\n", getenv("DUMP"));
    }
    /* hyperplane assignment per fibre, then hubs */
    int hcnt[66] = {0}, hyp_of[64][12];
    for (int l = 0; l < npts; l++) for (int qq = 0; qq < 3; qq++) for (int i = 0; i < 4; i++) { int fb = Q[Phi[l][qq]][i] / 5; hyp_of[l][qq * 4 + i] = hcnt[fb]++; }
    FILE *g = fopen(argv[7], "w");
    for (int j = 0; j < COP; j++) for (int l = 0; l < npts; l++) {      /* connector index j*13 + l */
        for (int qq = 0; qq < 3; qq++) for (int hb = 0; hb < 4; hb++) {
            for (int i = 0; i < 4; i++) { int fb = Q[Phi[l][qq]][i] / 5, dsel = Q[Phi[l][qq]][i] % 5, h = hyp_of[l][qq * 4 + i], s2 = slab_of_hyp[fb][h][j];
                /* the 4 lines of slab s2: take the (hb+i) mod 4-th line (a Latin assignment) */
                int lids[4], nlid = 0; for (int k = 0; k < 16; k++) { int li = lineid5[fb][dsel][slabpts[fb][s2][k]]; int seen = 0; for (int t = 0; t < nlid; t++) if (lids[t] == li) seen = 1; if (!seen) lids[nlid++] = li; }
                int want = lids[(hb + i) % 4];
                for (int k = 0; k < 16; k++) if (lineid5[fb][dsel][slabpts[fb][s2][k]] == want) fprintf(g, "%d ", fb * 256 + slabpts[fb][s2][k] + (side == 0 ? H : 0)); }
            fprintf(g, "\n"); } }
    fclose(g);
    printf("wrote %d hubs\n", COP * npts * 12);
    return 0;
}
