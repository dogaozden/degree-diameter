/* b13: Haar graphs H(G,S) on G = SL(2,8) x SL(2,8) x Z_19 (order N = 4,826,304), Delta = 6, D = 12.
 * Automorphism sigma(x,y,z) = (F(x), F(y), 7z), F = entrywise Frobenius of GF(8) (order 3), 7 has order 3 mod 19.
 * Fix(sigma) = SL(2,2)^2 x {0} (36 elements).
 * Criterion (even D, vertex-transitive on each side): from (e,A) every B-vertex within odd distance <= 11.
 * cost = number of B-vertices not reached within distance 11 (holes).
 *
 * Usage: haar_prod3 MODE SECS SEED OUT
 *   MODE R : unstructured random 6-sets (statistics)
 *   MODE T : two free sigma-orbits (orbit-closed S)
 *   MODE E : {e, f1, f2} + one free orbit (e and two fixed points)
 *   MODE A : annealing over two-orbit states (replace one orbit), starting from random
 * Prints a histogram of costs; writes OUT (the set S, element codes) on cost 0.
 * Memory: visA, visB (N bytes each) + two int frontier arrays (N ints each), about 50 MB.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

#define Q 8
#define NS 504
#define NZ 19
#define N (NS * NS * NZ)
#define DEG 6

static unsigned short mt[NS][NS];
static unsigned short inv_[NS];
static unsigned short fr[NS];
static int idSL;
static unsigned char *visA, *visB;
static int *fA, *fB;

static int gfmul(int a, int b) {
    int r = 0;
    for (int i = 0; i < 3; i++) if (b & (1 << i)) r ^= a << i;
    for (int i = 4; i >= 3; i--) if (r & (1 << i)) r ^= 0xB << (i - 3); /* x^3 = x + 1 */
    return r;
}

static int mat_code(int a, int b, int c, int d) { return a + 8 * b + 64 * c + 512 * d; }

static void build_sl(void) {
    static int idx_of[4096];
    static int mats[NS][4];
    int cnt = 0;
    for (int i = 0; i < 4096; i++) idx_of[i] = -1;
    for (int a = 0; a < 8; a++) for (int b = 0; b < 8; b++) for (int c = 0; c < 8; c++) for (int d = 0; d < 8; d++) {
        if ((gfmul(a, d) ^ gfmul(b, c)) == 1) {
            mats[cnt][0] = a; mats[cnt][1] = b; mats[cnt][2] = c; mats[cnt][3] = d;
            idx_of[mat_code(a, b, c, d)] = cnt;
            cnt++;
        }
    }
    if (cnt != NS) { fprintf(stderr, "SL(2,8) count %d\n", cnt); exit(1); }
    for (int i = 0; i < NS; i++) {
        int a = mats[i][0], b = mats[i][1], c = mats[i][2], d = mats[i][3];
        if (a == 1 && b == 0 && c == 0 && d == 1) idSL = i;
        int fa = gfmul(a, a), fb = gfmul(b, b), fc = gfmul(c, c), fd = gfmul(d, d);
        fr[i] = (unsigned short)idx_of[mat_code(fa, fb, fc, fd)];
    }
    for (int i = 0; i < NS; i++) for (int j = 0; j < NS; j++) {
        int a = mats[i][0], b = mats[i][1], c = mats[i][2], d = mats[i][3];
        int e = mats[j][0], f = mats[j][1], g = mats[j][2], h = mats[j][3];
        int A = gfmul(a, e) ^ gfmul(b, g);
        int B = gfmul(a, f) ^ gfmul(b, h);
        int C = gfmul(c, e) ^ gfmul(d, g);
        int D = gfmul(c, f) ^ gfmul(d, h);
        mt[i][j] = (unsigned short)idx_of[mat_code(A, B, C, D)];
    }
    for (int i = 0; i < NS; i++) for (int j = 0; j < NS; j++) if (mt[i][j] == idSL) inv_[i] = (unsigned short)j;
}

static inline int enc(int x, int y, int z) { return (x * NS + y) * NZ + z; }

static int sigma(int g) {
    int z = g % NZ, r = g / NZ, y = r % NS, x = r / NS;
    return enc(fr[x], fr[y], (7 * z) % NZ);
}

static int rnd_seed_state;
static inline unsigned long long xrand(void) {
    /* splitmix64 */
    unsigned long long z = (unsigned long long)(rnd_seed_state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static inline int rnd_int(int m) { return (int)(xrand() % (unsigned long long)m); }

/* holes: BFS over the bipartite Haar graph from (e,A) to odd distance 11 */
static int holes(const int *S) {
    int sx[DEG], sy[DEG], sz[DEG], ix[DEG], iy[DEG], iz[DEG];
    for (int k = 0; k < DEG; k++) {
        int g = S[k], z = g % NZ, r = g / NZ, y = r % NS, x = r / NS;
        sx[k] = x; sy[k] = y; sz[k] = z;
        ix[k] = inv_[x]; iy[k] = inv_[y]; iz[k] = (NZ - z) % NZ;
    }
    memset(visA, 0, N);
    memset(visB, 0, N);
    int e = enc(idSL, idSL, 0);
    int nA = 0, nB = 0, cntB = 0;
    fA[nA++] = e; visA[e] = 1;
    for (int t = 0; t < 6; t++) {
        /* A -> B (distance 2t+1) */
        nB = 0;
        for (int i = 0; i < nA; i++) {
            int g = fA[i], z = g % NZ, r = g / NZ, y = r % NS, x = r / NS;
            for (int k = 0; k < DEG; k++) {
                int h = enc(mt[sx[k]][x], mt[sy[k]][y], (sz[k] + z) % NZ);
                if (!visB[h]) { visB[h] = 1; fB[nB++] = h; cntB++; }
            }
        }
        if (t == 5) break;
        /* B -> A (distance 2t+2) */
        nA = 0;
        for (int i = 0; i < nB; i++) {
            int h = fB[i], z = h % NZ, r = h / NZ, y = r % NS, x = r / NS;
            for (int k = 0; k < DEG; k++) {
                int g = enc(mt[ix[k]][x], mt[iy[k]][y], (iz[k] + z) % NZ);
                if (!visA[g]) { visA[g] = 1; fA[nA++] = g; }
            }
        }
    }
    return N - cntB;
}

/* a random free sigma-orbit (size 3) as three codes */
static void rand_orbit(int *o) {
    for (;;) {
        int g = rnd_int(N);
        int s1 = sigma(g), s2 = sigma(s1);
        if (s1 == g) continue;
        o[0] = g; o[1] = s1; o[2] = s2;
        return;
    }
}

static int fix_list[64], nfix = 0;

static void build_fix(void) {
    /* Fix(sigma) = SL(2,2)^2 x {0}: elements with entries in GF(2) */
    fix_list[nfix++] = enc(idSL, idSL, 0); /* identity first */
    for (int x = 0; x < NS; x++) for (int y = 0; y < NS; y++) {
        /* x fixed under F iff entries in GF(2) */
        int xi = x, yi = y;
        if (xi == idSL && yi == idSL) continue;
        if (fr[xi] == xi && fr[yi] == yi) {
            if (nfix < 64) fix_list[nfix++] = enc(xi, yi, 0);
        }
    }
}

static int same_set_ok(const int *S) {
    for (int i = 0; i < DEG; i++) for (int j = i + 1; j < DEG; j++) if (S[i] == S[j]) return 0;
    return 1;
}

static void print_set(FILE *f, const int *S) {
    for (int k = 0; k < DEG; k++) {
        int g = S[k], z = g % NZ, r = g / NZ, y = r % NS, x = r / NS;
        fprintf(f, "%d %d %d\n", x, y, z);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: haar_prod3 MODE SECS SEED OUT\n"); return 1; }
    char mode = argv[1][0];
    double secs = atof(argv[2]);
    rnd_seed_state = atoi(argv[3]);
    const char *out = argv[4];
    build_sl();
    build_fix();
    visA = malloc(N); visB = malloc(N);
    fA = malloc(sizeof(int) * (size_t)N); fB = malloc(sizeof(int) * (size_t)N);
    if (!visA || !visB || !fA || !fB) { fprintf(stderr, "alloc\n"); return 1; }
    fprintf(stderr, "N=%d 2N=%d idSL=%d |Fix|(sigma on SL^2 x 0)=%d\n", N, 2 * N, idSL, nfix);
    /* sanity: sigma is an automorphism of order 3 on random elements */
    for (int t = 0; t < 1000; t++) {
        int a = rnd_int(N), b = rnd_int(N);
        int ab = 0;
        /* product (a*b) computed componentwise */
        int az = a % NZ, ar = a / NZ, ay = ar % NS, ax = ar / NS;
        int bz = b % NZ, br = b / NZ, by = br % NS, bx = br / NS;
        ab = enc(mt[ax][bx], mt[ay][by], (az + bz) % NZ);
        int lhs = sigma(ab);
        int rhs_a = sigma(a), rhs_b = sigma(b);
        int rz = rhs_a % NZ, rr = rhs_a / NZ, ry = rr % NS, rx = rr / NS;
        int qz = rhs_b % NZ, qr = rhs_b / NZ, qy = qr % NS, qx = qr / NS;
        int rhs = enc(mt[rx][qx], mt[ry][qy], (rz + qz) % NZ);
        if (lhs != rhs) { fprintf(stderr, "sigma not a hom\n"); return 1; }
        if (sigma(sigma(sigma(a))) != a) { fprintf(stderr, "sigma order\n"); return 1; }
    }

    double t0 = now();
    int hist[64] = {0};
    int best = 1 << 30, bestS[DEG];
    int nsamp = 0;

    if (mode == 'R' || mode == 'T' || mode == 'E') {
        while ((now() - t0) < secs) {
            int S[DEG];
            if (mode == 'R') {
                for (int k = 0; k < DEG; k++) S[k] = rnd_int(N);
                if (!same_set_ok(S)) continue;
            } else if (mode == 'T') {
                int o1[3], o2[3];
                rand_orbit(o1); rand_orbit(o2);
                for (int k = 0; k < 3; k++) { S[k] = o1[k]; S[3 + k] = o2[k]; }
                if (!same_set_ok(S)) continue;
            } else {
                int o[3];
                rand_orbit(o);
                S[0] = enc(idSL, idSL, 0);
                S[1] = fix_list[1 + rnd_int(nfix - 1)];
                do { S[2] = fix_list[1 + rnd_int(nfix - 1)]; } while (S[2] == S[1]);
                S[3] = o[0]; S[4] = o[1]; S[5] = o[2];
                if (!same_set_ok(S)) continue;
            }
            int c = holes(S);
            nsamp++;
            if (c < 64) hist[c]++; else hist[63]++;
            if (c < best) {
                best = c; memcpy(bestS, S, sizeof S);
                fprintf(stderr, "sample %d best cost %d (t=%.1fs)\n", nsamp, c, (now() - t0));
            }
            if (c == 0) {
                FILE *f = fopen(out, "w");
                fprintf(f, "# b13 Haar graph on SL(2,8)xSL(2,8)xZ19, elements as x y z; mode %c seed %s\n", mode, argv[3]);
                print_set(f, S);
                fclose(f);
                fprintf(stderr, "COST 0 FOUND, written to %s\n", out);
                break;
            }
        }
        printf("mode %c samples %d best %d\nhist:", mode, nsamp, best);
        for (int c = 0; c < 64; c++) if (hist[c]) printf(" %d:%d", c, hist[c]);
        printf("\n");
    } else if (mode == 'A') {
        /* annealing over two free orbits */
        int cur[DEG], cand[DEG];
        int o1[3], o2[3];
        rand_orbit(o1); rand_orbit(o2);
        for (int k = 0; k < 3; k++) { cur[k] = o1[k]; cur[3 + k] = o2[k]; }
        while (!same_set_ok(cur)) { rand_orbit(o1); rand_orbit(o2); for (int k = 0; k < 3; k++) { cur[k] = o1[k]; cur[3 + k] = o2[k]; } }
        int cc = holes(cur);
        best = cc; memcpy(bestS, cur, sizeof cur);
        long moves = 0;
        while ((now() - t0) < secs) {
            memcpy(cand, cur, sizeof cur);
            int o[3];
            rand_orbit(o);
            int slot = rnd_int(2);
            for (int k = 0; k < 3; k++) cand[3 * slot + k] = o[k];
            if (!same_set_ok(cand)) continue;
            int c = holes(cand);
            moves++;
            if (c <= cc) { memcpy(cur, cand, sizeof cur); cc = c; }
            if (cc < best) {
                best = cc; memcpy(bestS, cur, sizeof cur);
                fprintf(stderr, "move %ld best %d\n", moves, best);
            }
            if (cc == 0) {
                FILE *f = fopen(out, "w");
                fprintf(f, "# b13 Haar graph on SL(2,8)xSL(2,8)xZ19, elements as x y z; annealing\n");
                print_set(f, cur);
                fclose(f);
                fprintf(stderr, "COST 0 FOUND, written to %s\n", out);
                break;
            }
        }
        printf("mode A moves %ld best %d\n", moves, best);
    }
    printf("time %.1f s, best S (x y z):", (now() - t0));
    for (int k = 0; k < DEG; k++) {
        int g = bestS[k], z = g % NZ, r = g / NZ, y = r % NS, x = r / NS;
        printf(" (%d,%d,%d)", x, y, z);
    }
    printf("\n");
    return 0;
}
