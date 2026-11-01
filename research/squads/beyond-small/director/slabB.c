/* slabB: step B of the slab design (director, job beyond-small). One side at a time.
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
static int slabid[66][256], hypid[66][256], lineid[66][256];   /* coset ids within the fibre */
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
    if (getenv("COVERTEST")) {
        int NL = 66 * 64; int (*LL)[4] = malloc(sizeof(int[4]) * NL); uint64_t *LBall = malloc((size_t)NL * W * 8);
        for (int fb = 0; fb < 66; fb++) for (int y = 0; y < 256; y++) { int li = lineid[fb][y]; int idx = fb * 64 + li; static int cnt[66 * 64]; LL[idx][cnt[idx]++] = fb * 256 + y; }
        for (int i = 0; i < NL; i++) { uint64_t *o = LBall + (size_t)i * W; memset(o, 0, W * 8); for (int m = 0; m < 4; m++) { uint64_t *bl = ball + (size_t)LL[i][m] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
        int succ = 0, tries = 300; long offs_ok = 0, offs_tot = 0; long hist[67] = {0}; long minunc = 1 << 30, sumunc = 0;
        for (int t = 0; t < tries; t++) { int ch[4]; uint64_t unc[W]; for (int w = 0; w < W; w++) unc[w] = ~0ULL;
            for (int k = 0; k < 4; k++) { int bi = -1, bg = -1;
                for (int s2 = 0; s2 < (k == 0 ? 1 : NL); s2++) { int i = k == 0 ? (int)(rnd() % NL) : s2; int gg = 0; uint64_t *o = LBall + (size_t)i * W; for (int w = 0; w < W; w++) gg += __builtin_popcountll(unc[w] & o[w]); if (gg > bg) { bg = gg; bi = i; } }
                ch[k] = bi; uint64_t *o = LBall + (size_t)bi * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w]; }
            int left = popw(unc); if (left == 0) succ++; if (left < minunc) minunc = left; sumunc += left;
            if (left == 0 && succ <= 5) printf("cover fibres %d %d %d %d\n", ch[0] / 64, ch[1] / 64, ch[2] / 64, ch[3] / 64);
            if (left == 0) { int keep = 0; for (int r = 0; r < 40; r++) { uint64_t u2[W]; for (int w = 0; w < W; w++) u2[w] = ~0ULL;
                    for (int k = 0; k < 4; k++) { int i = (ch[k] / 64) * 64 + (int)(rnd() % 64); uint64_t *o = LBall + (size_t)i * W; for (int w = 0; w < W; w++) u2[w] &= ~o[w]; }
                    if (popw(u2) == 0) keep++; }
                offs_ok += keep; offs_tot += 40; } }
        printf("offset test: random parallel lines in the same 4 fibres still cover in %ld of %ld trials\n", offs_ok, offs_tot);
        printf("COVERTEST: %d of %d greedy 4-line covers from slab-direction lines succeed; min uncovered %ld, mean %.1f\n", succ, tries, minunc, (double)sumunc / tries);
        return 0;
    }
    /* 1. domination: choose F_l (NDOM fibres per line), greedily per root, respecting 4 hyperplanes per fibre */
    int Fl[64][32], nF[64] = {0}, hypuse[66] = {0}, hypline[66][4];
    for (int rep = 0; rep < 1; rep++) {
        for (int l = 0; l < npts; l++) nF[l] = 0; memset(hypuse, 0, sizeof hypuse);
        for (int round = 0; round < NDOM; round++) for (int l = 0; l < npts; l++) {
            /* pick the fibre that adds most S-fibres to the worst root on this line */
            int bestf = -1; double bsc = -1;
            for (int fb = 0; fb < 66; fb++) { if (hypuse[fb] >= 4) continue; int dup = 0; for (int i = 0; i < nF[l]; i++) if (Fl[l][i] == fb) dup = 1; if (dup) continue;
                double sc = 0;
                for (int k = 0; k < K; k++) { int R = lines[l][k]; uint64_t cov[2] = {0, 0};
                    for (int m = 0; m < npts; m++) { int on = 0; for (int kk = 0; kk < K; kk++) if (lines[m][kk] == R) on = 1; if (!on) continue;
                        for (int i = 0; i < nF[m]; i++) { cov[0] |= ctrlN[Fl[m][i]][0]; cov[1] |= ctrlN[Fl[m][i]][1]; } }
                    int gain = __builtin_popcountll(ctrlN[fb][0] & ~cov[0]) + __builtin_popcountll(ctrlN[fb][1] & ~cov[1]);
                    int have = __builtin_popcountll(cov[0]) + __builtin_popcountll(cov[1]);
                    sc += gain * (1.0 + (66 - have) / 10.0); }
                sc += (rnd() % 100) / 1000.0;
                if (sc > bsc) { bsc = sc; bestf = fb; } }
            Fl[l][nF[l]++] = bestf; hypline[bestf][hypuse[bestf]++] = l;
        }
    }
    int worst = 99;
    for (int R = 0; R < npts; R++) { uint64_t cov[2] = {0, 0};
        for (int m = 0; m < npts; m++) { int on = 0; for (int kk = 0; kk < K; kk++) if (lines[m][kk] == R) on = 1; if (!on) continue;
            for (int i = 0; i < nF[m]; i++) { cov[0] |= ctrlN[Fl[m][i]][0]; cov[1] |= ctrlN[Fl[m][i]][1]; } }
        int c = __builtin_popcountll(cov[0]) + __builtin_popcountll(cov[1]); if (c < worst) worst = c; }
    printf("domination: worst root covers %d of 66 S-fibres (NDOM %d per line)\n", worst, NDOM);
    /* slab ownership: -1 free; hyperplane slabs reserved */
    static int owner[66][16]; for (int fb = 0; fb < 66; fb++) for (int s = 0; s < 16; s++) owner[fb][s] = -1;
    int NC = COP * npts;
    int cslab_f[512][16], cslab_s[512][16], ncs[512];
    for (int c = 0; c < NC; c++) ncs[c] = 0;
    for (int fb = 0; fb < 66; fb++) for (int h = 0; h < hypuse[fb]; h++) { int l = hypline[fb][h];
        for (int j = 0; j < COP && j < 4; j++) { int c = j * npts + l, s = slab_of_hyp[fb][h][j]; owner[fb][s] = c; cslab_f[c][ncs[c]] = fb; cslab_s[c][ncs[c]] = s; ncs[c]++; } }
    /* 2. coverage: complete each connector to 12 slabs at distinct fibres covering all T-fibres */
    int uncov_total = 0;
    for (int c = 0; c < NC; c++) {
        while (ncs[c] < 12) {
            uint64_t cov[2] = {0, 0}; for (int i = 0; i < ncs[c]; i++) { cov[0] |= slabD2[cslab_f[c][i]][cslab_s[c][i]][0]; cov[1] |= slabD2[cslab_f[c][i]][cslab_s[c][i]][1]; }
            int bf = -1, bs = -1, bg = -1;
            for (int fb = 0; fb < 66; fb++) { int dup = 0; for (int i = 0; i < ncs[c]; i++) if (cslab_f[c][i] == fb) dup = 1; if (dup) continue;
                for (int s = 0; s < 16; s++) { if (owner[fb][s] >= 0) continue; int hres = 0; for (int h = 0; h < hypuse[fb]; h++) for (int j = 0; j < 4; j++) if (slab_of_hyp[fb][h][j] == s) hres = 1; if (hres) continue;
                    int g = __builtin_popcountll(slabD2[fb][s][0] & ~cov[0]) + __builtin_popcountll(slabD2[fb][s][1] & ~cov[1]);
                    g = g * 64 + (rnd() & 63); if (g > bg) { bg = g; bf = fb; bs = s; } } }
            if (bf < 0) break;
            owner[bf][bs] = c; cslab_f[c][ncs[c]] = bf; cslab_s[c][ncs[c]] = bs; ncs[c]++;
        }
        uint64_t cov[2] = {0, 0}; for (int i = 0; i < ncs[c]; i++) { cov[0] |= slabD2[cslab_f[c][i]][cslab_s[c][i]][0]; cov[1] |= slabD2[cslab_f[c][i]][cslab_s[c][i]][1]; }
        uncov_total += 66 - __builtin_popcountll(cov[0]) - __builtin_popcountll(cov[1]);
    }
    printf("coverage: %d connectors, total uncovered T-fibres over all connectors %d\n", NC, uncov_total);
    /* 3. hubs: split each connector's 48 lines into 12 covering quadruples */
    FILE *g = fopen(argv[7], "w"); int badhubs = 0;
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL;
    for (int c = 0; c < NC; c++) {
        int L[48][4], nl = 0; uint64_t (*LB)[W] = malloc(sizeof(uint64_t[W]) * 48);
        for (int i = 0; i < ncs[c]; i++) { int fb = cslab_f[c][i], s = cslab_s[c][i]; int seenl[64] = {0};
            for (int k = 0; k < 16; k++) { int y = slabpts[fb][s][k], li = lineid[fb][y]; if (seenl[li]) continue; seenl[li] = 1;
                int m = 0; for (int k2 = 0; k2 < 16; k2++) if (lineid[fb][slabpts[fb][s][k2]] == li) L[nl][m++] = fb * 256 + slabpts[fb][s][k2];
                memset(LB[nl], 0, sizeof(uint64_t) * W); for (int m2 = 0; m2 < 4; m2++) { uint64_t *bl = ball + (size_t)L[nl][m2] * W; for (int w = 0; w < W; w++) LB[nl][w] |= bl[w]; }
                nl++; } }
        int bestgroups[12][4], bestok = -1;
        for (int att = 0; att < 4000 && bestok < 12; att++) {
            int used[48] = {0}, groups[12][4], ok = 0, ng = 0;
            for (int hb = 0; hb < 12; hb++) {
                int first = -1; for (int t = 0; t < 48; t++) { int i = rnd() % nl; if (!used[i]) { first = i; break; } } if (first < 0) for (int i = 0; i < nl; i++) if (!used[i]) { first = i; break; }
                if (first < 0) break;
                uint64_t unc[W]; for (int w = 0; w < W; w++) unc[w] = ~LB[first][w];
                int grp[4] = {first, -1, -1, -1}; used[first] = 1;
                for (int k = 1; k < 4; k++) { int bi = -1, bg = -1;
                    for (int i = 0; i < nl; i++) { if (used[i]) continue; int gg = 0; for (int w = 0; w < W; w++) gg += __builtin_popcountll(unc[w] & LB[i][w]); gg = gg * 8 + (rnd() & 7); if (gg > bg) { bg = gg; bi = i; } }
                    grp[k] = bi; used[bi] = 1; for (int w = 0; w < W; w++) unc[w] &= ~LB[bi][w]; }
                if (popw(unc) == 0) ok++;
                memcpy(groups[ng++], grp, sizeof grp);
            }
            if (ok > bestok) { bestok = ok; memcpy(bestgroups, groups, sizeof groups); }
        }
        badhubs += 12 - bestok;
        for (int hb = 0; hb < 12; hb++) { for (int k = 0; k < 4; k++) for (int m = 0; m < 4; m++) fprintf(g, "%d ", L[bestgroups[hb][k]][m] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
        free(LB);
    }
    fclose(g);
    printf("hubs: %d connectors x 12, non-covering hubs %d\n", NC, badhubs);
    return 0;
}
