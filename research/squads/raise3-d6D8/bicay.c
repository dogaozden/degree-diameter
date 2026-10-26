/*
 * bicay: simulated annealing for 2-fiber bi-Cayley (voltage) lifts of degree d and diameter D.
 *
 * Group G = H x Z_n (H from mkgroup.py, n <= 64). Vertices (g, s, i): g in G, side s in {0,1}, fiber i in {0,1}.
 * Edges: (g,0,i) ~ (a*g, 1, j) for a in S[i][j]. Block sizes: |S00| = |S11| = A, |S01| = |S10| = d - A.
 * So each vertex has degree d and the graph has 4|G| vertices. A solution has diameter <= D.
 *
 * Cost = sum over the 4 fiber roots (e, s, i) of the number of vertices at distance > D from that root.
 * G acts regularly on each fiber by right multiplication, so the 4 roots see every pair of vertices.
 * Cost 0 means diameter <= D. The BFS is bit-parallel: a set of G is H rows of n bits; left multiplication by
 * (a,c) maps row h to row a*h and rotates its bits by c.
 *
 * usage: bicay GROUP.bin n A d D seconds seed outfile
 * env: TMAX TMIN CYC (steps per cooling cycle), THREADS ignored.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXD 16
static int H, n, D, d, A;
static uint16_t *MH;
static int *INV;
static uint64_t MASK;
static int bsz[4];
static int vol[4][MAXD];          /* code = h*n + z, block b = 2*i + j */
static uint64_t *Fr[4], *Vis[4], *Nx[4];
static unsigned long long rs = 88172645463325252ULL;
static int bestvol[4][MAXD];

static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static inline uint64_t rot(uint64_t x, int c) {
    if (!c) return x;
    return ((x << c) | (x >> (n - c))) & MASK;
}

/* out[a*h] |= (in[h] rotated by c) : left multiplication by the element (a,c) of G */
static inline void applyL(uint64_t *out, const uint64_t *in, int a, int c) {
    const uint16_t *row = MH + (size_t)a * H;
    for (int h = 0; h < H; h++) {
        uint64_t x = in[h];
        if (x) out[row[h]] |= rot(x, c);
    }
}

static inline int popc(uint64_t x) { return __builtin_popcountll(x); }

/* uncovered count from root fiber rf (= 2*side + fiber) */
static long long bfs_uncov(int rf) {
    for (int f = 0; f < 4; f++) { memset(Fr[f], 0, H * 8); memset(Vis[f], 0, H * 8); }
    Fr[rf][0] = 1ULL; Vis[rf][0] = 1ULL;   /* identity: row 0 (h = 0 is the identity), bit 0 */
    int active[4] = {0, 0, 0, 0}; active[rf] = 1;
    for (int lev = 1; lev <= D; lev++) {
        for (int f = 0; f < 4; f++) memset(Nx[f], 0, H * 8);
        int any = 0;
        for (int f = 0; f < 4; f++) {
            if (!active[f]) continue;
            int s = f >> 1, i = f & 1;
            for (int j = 0; j < 2; j++) {
                int tf = 2 * (1 - s) + j;
                int b = (s == 0) ? 2 * i + j : 2 * j + i;   /* block of S[i][j] (s=0) or S[j][i] (s=1) */
                for (int k = 0; k < bsz[b]; k++) {
                    int code = vol[b][k];
                    int a = code / n, c = code % n;
                    if (s == 0) applyL(Nx[tf], Fr[f], a, c);
                    else applyL(Nx[tf], Fr[f], INV[a], (n - c) % n);
                }
            }
        }
        for (int f = 0; f < 4; f++) {
            active[f] = 0;
            uint64_t *nx = Nx[f], *v = Vis[f], *fr = Fr[f];
            for (int h = 0; h < H; h++) {
                uint64_t x = nx[h] & ~v[h];
                fr[h] = x; v[h] |= x;
                if (x) active[f] = 1;
            }
            any |= active[f];
        }
        if (!any) break;
    }
    long long vis = 0;
    for (int f = 0; f < 4; f++) for (int h = 0; h < H; h++) vis += popc(Vis[f][h]);
    return 4LL * H * n - vis;
}

static long long cost(void) {
    long long c = 0;
    for (int rf = 0; rf < 4; rf++) c += bfs_uncov(rf);
    return c;
}

static int in_block(int b, int code, int skip) {
    for (int k = 0; k < bsz[b]; k++) if (k != skip && vol[b][k] == code) return 1;
    return 0;
}

/* orbit mode: block slot j = elements vol[b][j*K .. j*K+K-1], an orbit of sigma (exact size K) */
static int K = 1;
static int *ORB; static int NORB;        /* orbit list: NORB orbits, K codes each */

static int conflict(int b, const int *codes, int ncodes, int skip0, int skip1) {
    for (int k = 0; k < bsz[b]; k++) {
        if (k >= skip0 && k < skip1) continue;
        for (int t = 0; t < ncodes; t++) if (vol[b][k] == codes[t]) return 1;
    }
    return 0;
}

static void write_solution(const char *out, const char *grp) {
    FILE *fp = fopen(out, "w");
    if (!fp) { perror("out"); return; }
    fprintf(fp, "GROUP %s n %d A %d d %d D %d H %d\n", grp, n, A, d, D, H);
    /* block order: S00, S01, S10, S11 */
    const char *names[4] = {"S00", "S01", "S10", "S11"};
    for (int b = 0; b < 4; b++) {
        fprintf(fp, "%s", names[b]);
        for (int k = 0; k < bsz[b]; k++) fprintf(fp, " %d", vol[b][k]);
        fprintf(fp, "\n");
    }
    fclose(fp);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: bicay GROUP.bin n A d D seconds seed outfile   (env: K SIGMA_H SIGMA_U CONFIG TMAX TMIN CYC)\n"); return 2; }
    const char *grp = argv[1];
    n = atoi(argv[2]); A = atoi(argv[3]); d = atoi(argv[4]); D = atoi(argv[5]);
    double secs = atof(argv[6]);
    rs ^= (unsigned long long)atoll(argv[7]) * 0x9E3779B97F4A7C15ULL + 1;
    const char *out = argv[8];
    if (n < 1 || n > 64 || d > MAXD || A < 1 || A >= d) { fprintf(stderr, "bad params\n"); return 2; }
    MASK = (n == 64) ? ~0ULL : ((1ULL << n) - 1);
    FILE *fp = fopen(grp, "rb");
    if (!fp) { perror("group"); return 2; }
    uint32_t h32; if (fread(&h32, 4, 1, fp) != 1) return 2;
    H = (int)h32;
    MH = malloc((size_t)H * H * 2);
    if (fread(MH, 2, (size_t)H * H, fp) != (size_t)H * H) { fprintf(stderr, "short group file\n"); return 2; }
    fclose(fp);
    INV = malloc(sizeof(int) * H);
    for (int a = 0; a < H; a++) for (int b = 0; b < H; b++) if (MH[(size_t)a * H + b] == 0) INV[a] = b;
    for (int f = 0; f < 4; f++) { Fr[f] = aligned_alloc(64, ((H * 8 + 63) / 64) * 64); Vis[f] = aligned_alloc(64, ((H * 8 + 63) / 64) * 64); Nx[f] = aligned_alloc(64, ((H * 8 + 63) / 64) * 64); }
    int TOT = H * n;
    bsz[0] = A; bsz[1] = d - A; bsz[2] = d - A; bsz[3] = A;
    K = getenv("K") ? atoi(getenv("K")) : 1;
    if (K < 1) K = 1;
    for (int b = 0; b < 4; b++) if (bsz[b] % K) { fprintf(stderr, "block size %d not a multiple of K=%d\n", bsz[b], K); return 2; }
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 2.0;
    double TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.2;
    long long CYC = getenv("CYC") ? atoll(getenv("CYC")) : 300000;

    /* sigma(h,z) = (alpha(h), U*z), alpha read from SIGMA_H (one integer per line) */
    int *sigma = malloc(sizeof(int) * TOT);
    for (int c = 0; c < TOT; c++) sigma[c] = c;
    if (K > 1 || getenv("SIGMA_H")) {
        int U = getenv("SIGMA_U") ? atoi(getenv("SIGMA_U")) : 1;
        int *alpha = malloc(sizeof(int) * H);
        if (getenv("SIGMA_H")) {
            FILE *af = fopen(getenv("SIGMA_H"), "r");
            if (!af) { perror("SIGMA_H"); return 2; }
            for (int h = 0; h < H; h++) if (fscanf(af, "%d", &alpha[h]) != 1) { fprintf(stderr, "short SIGMA_H\n"); return 2; }
            fclose(af);
        } else for (int h = 0; h < H; h++) alpha[h] = h;
        for (int h = 0; h < H; h++) for (int z = 0; z < n; z++) sigma[h * n + z] = alpha[h] * n + (int)(((long long)U * z) % n);
        free(alpha);
    }
    /* orbits of sigma of size exactly K (K = 1: every code is an orbit) */
    int *seen = calloc(TOT, sizeof(int));
    ORB = malloc(sizeof(int) * (size_t)TOT);
    NORB = 0;
    for (int c = 0; c < TOT; c++) {
        if (seen[c]) continue;
        int orb[MAXD * 0 + 64]; int L = 0; int x = c;
        do { if (L < 64) orb[L] = x; L++; seen[x] = 1; x = sigma[x]; } while (x != c && L <= 64);
        if (L == K && x == c) { for (int t = 0; t < K; t++) ORB[(size_t)NORB * K + t] = orb[t]; NORB++; }
    }
    fprintf(stderr, "orbits of size %d: %d (|G|=%d)\n", K, NORB, TOT);
    if (NORB == 0) { fprintf(stderr, "no orbits\n"); return 2; }
    if (getenv("CONFIG")) {   /* evaluate the cost of the voltage sets in file CONFIG and exit */
        FILE *cf = fopen(getenv("CONFIG"), "r");
        if (!cf) { perror("config"); return 2; }
        char line[65536], nm[8];
        if (!fgets(line, sizeof line, cf)) return 2;   /* header line */
        for (int b = 0; b < 4 && fgets(line, sizeof line, cf); b++) {
            char *p = line; int off;
            sscanf(p, "%7s%n", nm, &off); p += off;
            for (int k = 0; k < bsz[b]; k++) { int c; sscanf(p, "%d%n", &c, &off); p += off; vol[b][k] = c; }
        }
        fclose(cf);
        printf("COST %lld\n", cost());
        return 0;
    }
    rs ^= 0x12345ULL;
    for (int b = 0; b < 4; b++) for (int j = 0; j < bsz[b] / K; j++) {
        int tries = 0;
        while (1) {
            int o = rnd() % NORB;
            if (!conflict(b, ORB + (size_t)o * K, K, j * K, j * K + K)) {
                for (int t = 0; t < K; t++) vol[b][j * K + t] = ORB[(size_t)o * K + t];
                break;
            }
            if (++tries > 100000) { fprintf(stderr, "cannot place orbit\n"); return 2; }
        }
    }
    long long cur = cost(), best = cur;
    memcpy(bestvol, vol, sizeof vol);
    fprintf(stderr, "group %s |G|=%d (H=%d n=%d) A=%d d=%d D=%d K=%d start cost %lld\n", grp, TOT, H, n, A, d, D, K, cur);
    double t0 = now(); long long steps = 0; double tlog = t0;
    int oldv[MAXD];
    while (1) {
        steps++;
        long long pos = steps % CYC;
        double T = TMAX * pow(TMIN / TMAX, (double)pos / (double)CYC);
        int b; do { b = rnd() % 4; } while (bsz[b] == 0);
        int j = rnd() % (bsz[b] / K);
        int o = rnd() % NORB;
        if (conflict(b, ORB + (size_t)o * K, K, j * K, j * K + K)) continue;
        for (int t = 0; t < K; t++) { oldv[t] = vol[b][j * K + t]; vol[b][j * K + t] = ORB[(size_t)o * K + t]; }
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < best) { best = cur; memcpy(bestvol, vol, sizeof vol); }
            if (cur == 0) {
                write_solution(out, grp);
                fprintf(stderr, "SOLVED at step %lld (%.1f s): wrote %s\n", steps, now() - t0, out);
                printf("SOLVED %s n=%d A=%d d=%d D=%d K=%d steps=%lld time=%.1f file=%s\n", grp, n, A, d, D, K, steps, now() - t0, out);
                return 0;
            }
        } else {
            for (int t = 0; t < K; t++) vol[b][j * K + t] = oldv[t];
        }
        if (now() - tlog > 60) {
            tlog = now();
            fprintf(stderr, "  t=%.0f steps=%lld cur=%lld best=%lld T=%.3f\n", now() - t0, steps, cur, best, T);
        }
        if (now() - t0 > secs) break;
    }
    memcpy(vol, bestvol, sizeof vol);
    write_solution(out, grp);
    printf("NOSOLUTION %s n=%d A=%d d=%d D=%d K=%d steps=%lld best=%lld\n", grp, n, A, d, D, K, steps, best);
    return 1;
}
