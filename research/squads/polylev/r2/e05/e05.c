/* e05.c: random-walk greedy for disjoint totally singular lines of Q(6,16) (card e05, squad polylev r2).
   usage: e05 HEX OUTDIR SEED WALL_SECONDS T0
   Points: the N = 1118481 points of Q(6,16) with normalised 7-vectors over GF(16) in the encoding
   a0+2a1+4a2+8a3 (bit i = coefficient of x^i, x^4 = x+1, addition = XOR), as in research/d10D7/hexgen2.c.
   Hexagon lines from HEX are used only for the random walk p -> line -> point -> line -> point (incidence graph,
   so the end x is orthogonal to p). Candidate line = <p,x> = {p, x} u {p + l x : l in GF(16)*}, 17 points, taken iff
   all 17 are uncovered. Rounds: every uncovered point is tried T times; T is multiplied by 4 each round.
   Output (atomic, after every round and at exit): OUTDIR/sets_coords.txt (one line per set, 17 points, each point as
   7 hex digits = its normalised coordinates), OUTDIR/sets_ids.txt (same sets as point ids of HEX). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static uint8_t MUL[16][16], INV[16];
static int32_t N, L;
static int32_t *LINES, *PL, *SET;
static uint8_t *CO, *COV;
#define HB 22
#define HS (1u << HB)
static uint32_t *HK;
static int32_t *HV;
static uint64_t S[4];
static int32_t nl = 0;
static const char *HEXD = "0123456789abcdef";

static void die(const char *m) { fprintf(stderr, "e05: %s\n", m); exit(1); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static uint64_t sm(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static inline uint64_t rnd(void) {
    uint64_t r = rotl(S[1] * 5, 7) * 9, t = S[1] << 17;
    S[2] ^= S[0]; S[3] ^= S[1]; S[1] ^= S[2]; S[0] ^= S[3]; S[2] ^= t; S[3] = rotl(S[3], 45);
    return r;
}
static inline uint32_t rndn(uint32_t n) { return (uint32_t)(((rnd() >> 32) * (uint64_t)n) >> 32); }

static int gmul(int a, int b) {
    int r = 0;
    for (int i = 0; i < 4; i++) if ((b >> i) & 1) r ^= a << i;
    for (int k = 6; k >= 4; k--) if ((r >> k) & 1) r ^= 0x13 << (k - 4);   /* x^4+x+1 */
    return r;
}
static void field_init(void) {
    for (int a = 0; a < 16; a++) for (int b = 0; b < 16; b++) MUL[a][b] = (uint8_t)gmul(a, b);
    for (int a = 1; a < 16; a++) {
        int f = 0;
        for (int b = 1; b < 16; b++) if (MUL[a][b] == 1) { INV[a] = (uint8_t)b; f = 1; }
        if (!f) die("GF(16) tables: no inverse");
    }
}
static inline void norm(uint8_t *v) {   /* first nonzero coordinate becomes 1 */
    int i = 0;
    while (!v[i]) i++;
    uint8_t s = INV[v[i]];
    for (int j = 0; j < 7; j++) v[j] = MUL[s][v[j]];
}
static inline uint32_t keyof(const uint8_t *v) {
    return v[0] | (v[1] << 4) | (v[2] << 8) | (v[3] << 12) | (v[4] << 16) | (v[5] << 20) | ((uint32_t)v[6] << 24);
}
static inline uint32_t hh(uint32_t k) { return (k * 2654435761u) >> (32 - HB); }
static void hins(uint32_t k, int32_t id) {
    uint32_t h = hh(k);
    while (HK[h]) { if (HK[h] == k + 1) die("duplicate point key"); h = (h + 1) & (HS - 1); }
    HK[h] = k + 1; HV[h] = id;
}
static inline int32_t hfind(uint32_t k) {
    uint32_t h = hh(k);
    for (;;) {
        uint32_t e = HK[h];
        if (!e) return -1;
        if (e == k + 1) return HV[h];
        h = (h + 1) & (HS - 1);
    }
}

/* random walk p -> hexagon line -> point -> hexagon line -> point (4 incidence steps): end point x, orthogonal to p */
static inline int32_t walk(int32_t p) {
    const int32_t *pl = PL + (size_t)p * 17;
    int32_t L1 = pl[rndn(17)];
    const int32_t *ln1 = LINES + (size_t)L1 * 17;
    int k = 0; while (ln1[k] != p) k++;
    uint32_t r = rndn(16); int j = (int)r + (r >= (uint32_t)k);
    int32_t x1 = ln1[j];
    const int32_t *pl2 = PL + (size_t)x1 * 17;
    int32_t L2 = pl2[rndn(17)];
    const int32_t *ln2 = LINES + (size_t)L2 * 17;
    int k2 = 0; while (ln2[k2] != x1) k2++;
    r = rndn(16); j = (int)r + (r >= (uint32_t)k2);
    return ln2[j];
}

/* candidate line <p,x>: pts[0]=p, pts[1]=x, pts[2..16]=p+l x (l=1..15); true iff all 17 uncovered */
static int try_line(int32_t p, int32_t x, int32_t *pts) {
    if (COV[p] || COV[x]) return 0;
    pts[0] = p; pts[1] = x;
    const uint8_t *cp = CO + (size_t)p * 7, *cx = CO + (size_t)x * 7;
    for (int l = 1; l < 16; l++) {
        uint8_t v[7];
        for (int i = 0; i < 7; i++) v[i] = cp[i] ^ MUL[l][cx[i]];
        norm(v);
        int32_t id = hfind(keyof(v));
        if (id < 0) die("point p+lx not on the quadric list (field or quadric mismatch)");
        if (COV[id]) return 0;
        pts[l + 1] = id;
    }
    return 1;
}

static void write_sets(const char *dir) {
    char fin[4096], tmp[4096];
    snprintf(fin, sizeof fin, "%s/sets_coords.txt", dir); snprintf(tmp, sizeof tmp, "%s/.sets_coords.tmp", dir);
    FILE *f = fopen(tmp, "w"); if (!f) die("cannot write coords");
    for (int32_t s = 0; s < nl; s++)
        for (int k = 0; k < 17; k++) {
            int32_t id = SET[(size_t)s * 17 + k];
            for (int i = 0; i < 7; i++) fputc(HEXD[CO[(size_t)id * 7 + i]], f);
            fputc(k == 16 ? '\n' : ' ', f);
        }
    fclose(f); rename(tmp, fin);
    snprintf(fin, sizeof fin, "%s/sets_ids.txt", dir); snprintf(tmp, sizeof tmp, "%s/.sets_ids.tmp", dir);
    f = fopen(tmp, "w"); if (!f) die("cannot write ids");
    for (int32_t s = 0; s < nl; s++) {
        for (int k = 0; k < 17; k++) fprintf(f, "%d%c", SET[(size_t)s * 17 + k], k == 16 ? '\n' : ' ');
    }
    fclose(f); rename(tmp, fin);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: e05 HEX OUTDIR SEED WALL_SECONDS T0\n"); return 1; }
    const char *hex = argv[1], *dir = argv[2];
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double wall = atof(argv[4]);
    long T = atol(argv[5]);
    double t0 = now();
    field_init();

    FILE *f = fopen(hex, "rb"); if (!f) die("cannot open HEX");
    int32_t h[3];
    if (fread(h, 4, 3, f) != 3) die("short header");
    if (h[0] != 16) die("not q=16");
    N = h[1]; L = h[2];
    LINES = malloc((size_t)L * 17 * 4);
    CO = malloc((size_t)N * 7);
    if (!LINES || !CO) die("malloc");
    if (fread(LINES, 4, (size_t)L * 17, f) != (size_t)L * 17) die("short lines");
    if (fread(CO, 1, (size_t)N * 7, f) != (size_t)N * 7) die("short coords");
    fclose(f);
    fprintf(stderr, "loaded N=%d L=%d (%.1fs)\n", N, L, now() - t0);

    PL = malloc((size_t)N * 17 * 4);
    uint8_t *cnt = calloc(N, 1);
    for (int32_t l = 0; l < L; l++)
        for (int k = 0; k < 17; k++) {
            int32_t p = LINES[(size_t)l * 17 + k];
            if (cnt[p] >= 17) die("point on more than 17 lines");
            PL[(size_t)p * 17 + cnt[p]++] = l;
        }
    for (int32_t p = 0; p < N; p++) if (cnt[p] != 17) die("point not on 17 lines");
    free(cnt);

    HK = calloc(HS, 4); HV = malloc((size_t)HS * 4);
    for (int32_t p = 0; p < N; p++) {
        uint8_t v[7]; memcpy(v, CO + (size_t)p * 7, 7);
        norm(v);
        if (memcmp(v, CO + (size_t)p * 7, 7)) die("file coordinates not normalised");
        hins(keyof(v), p);
    }
    COV = calloc(N, 1);
    SET = malloc((size_t)(N / 17 + 2) * 17 * 4);
    int32_t *order = malloc((size_t)N * 4);
    for (int32_t i = 0; i < N; i++) order[i] = i;
    uint64_t sx = seed; for (int i = 0; i < 4; i++) S[i] = sm(&sx);
    fprintf(stderr, "index built (%.1fs)\n", now() - t0);

    int round = 0;
    int stop = 0;
    for (;;) {
        for (int32_t i = N - 1; i > 0; i--) { uint32_t j = rndn((uint32_t)i + 1); int32_t t = order[i]; order[i] = order[j]; order[j] = t; }
        long acc = 0;
        long unc0 = N - 17L * nl;
        int32_t pts[17];
        for (int32_t i = 0; i < N; i++) {
            if (now() - t0 > wall) { stop = 1; break; }
            int32_t p = order[i];
            if (COV[p]) continue;
            for (long t = 0; t < T; t++) {
                int32_t x = walk(p);
                if (x == p) continue;
                if (try_line(p, x, pts)) {
                    for (int k = 0; k < 17; k++) { COV[pts[k]] = 1; SET[(size_t)nl * 17 + k] = pts[k]; }
                    nl++; acc++;
                    break;
                }
            }
        }
        round++;
        write_sets(dir);
        fprintf(stderr, "round %d T=%ld sets=%d covered=%.4f (start-uncovered %ld, accepted %ld) t=%.1fs\n",
                round, T, nl, 17.0 * nl / N, unc0, acc, now() - t0);
        if (stop) break;
        if (unc0 - 17L * acc <= 0) break;
        T *= 4;
    }
    printf("sets=%d covered=%.6f time=%.1f\n", nl, 17.0 * nl / N, now() - t0);
    return 0;
}
