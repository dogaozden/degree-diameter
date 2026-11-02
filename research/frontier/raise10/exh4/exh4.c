/* exh4.c (job raise-d10, director, 2026-11-02): exhaustive search of Haar graphs H(G, {e,x,y,z}) of metacyclic groups
 * G = Z_m x|_r Z_k for (4, D) cells, built on the evaluation of research/frontier/beyond13/meta/hmeta.c (bit-parallel BFS
 * in inverse coordinates: right multiplication by a generator is a row shift plus a rotation).  See main() for the
 * symmetry reduction.  Build: gcc -O3 -march=native -o exh4 exh4.c -lm   (no OpenMP: single thread is fastest here) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <omp.h>
typedef uint64_t u64; typedef int64_t i64;
static i64 M, K_, R_, N; static int d, D;
static i64 *RP;               /* RP[j] = r^j mod m */
static i64 W, W2;             /* words per row (m bits), words per doubled row (2m bits + pad) */
static u64 *SA, *SB, *DBL;    /* current set (k rows of W words), next set, doubled source */
static i64 lastA = 0, lastB = 0;
static u64 *HA, *HB;          /* final reached sets of the last evaluation: side A run, side B run (for targeting) */
static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
typedef struct { i64 a, j; } el;
static i64 mpow(i64 b, i64 e, i64 m) { i64 x = 1 % m; b %= m; while (e) { if (e & 1) x = (__int128)x * b % m; b = (__int128)b * b % m; e >>= 1; } return x; }
static el inv(el x) { i64 jj = (K_ - x.j) % K_; el y = { (M - (__int128)RP[jj] * x.a % M) % M, jj }; return y; }
static u64 lastmask;
/* doubled copy of row j of src into DBL row j: bits [0,m) and [m,2m) */
static void make_dbl(const u64 *src) {
    #pragma omp parallel for schedule(static)
    for (i64 j = 0; j < K_; j++) {
        const u64 *s = src + j * W; u64 *t = DBL + j * W2;
        memset(t, 0, W2 * 8);
        memcpy(t, s, W * 8);
        i64 off = M; i64 q = off >> 6; int sh = off & 63;
        for (i64 w = 0; w < W; w++) {
            u64 v = s[w]; if (w == W - 1) v &= lastmask;
            t[q + w] |= sh ? (v << sh) : v;
            if (sh) t[q + w + 1] |= v >> (64 - sh);
        }
    }
}
/* dst row |= src row rotated by c: dst bit i = src bit (i - c mod m) = DBL bit (i + m - c) */
static inline void or_rot(u64 *dst, const u64 *dbl, i64 c) {
    i64 o = M - c; if (o <= 0) o += M;  /* o in (0, m] */
    i64 q = o >> 6; int sh = o & 63;
    if (sh == 0) for (i64 w = 0; w < W; w++) dst[w] |= dbl[q + w];
    else for (i64 w = 0; w < W; w++) dst[w] |= (dbl[q + w] >> sh) | (dbl[q + w + 1] << (64 - sh));
}
/* one step: dst = src * T (right multiplication by each generator in T); exh4: rotations from the tables ROT/JS */
static i64 *ROT[16]; static i64 JSH[16];
static void step(u64 *dst, const u64 *src, int base, int nt) {
    make_dbl(src);
    for (i64 J = 0; J < K_; J++) {
        u64 *t = dst + J * W; memset(t, 0, W * 8);
        for (int g = 0; g < nt; g++) {
            i64 j = J - JSH[base + g]; if (j < 0) j += K_;
            or_rot(t, DBL + j * W2, ROT[base + g][j]);
        }
        t[W - 1] &= lastmask;
    }
}
static i64 popc(const u64 *x) { i64 c = 0;
    #pragma omp parallel for reduction(+:c)
    for (i64 i = 0; i < K_ * W; i++) c += __builtin_popcountll(x[i]);
    return c; }
static el S[64], SI[64];
/* run D-1 steps from e on side `side` (0 = A: first step uses S^-1; 1 = B: first step uses S); return #reached on the
 * side reached after D-1 steps */
static i64 ball(int side) {
    memset(SA, 0, K_ * W * 8); SA[0] = 1;   /* element (0,0) = bit 0 of row 0 */
    u64 *cur = SA, *nx = SB; int useinv = (side == 0);
    for (int s = 0; s < D - 1; s++) {
        step(nx, cur, useinv ? d : 0, d);
        u64 *t = cur; cur = nx; nx = t; useinv = !useinv;
    }
    memcpy(side == 0 ? HA : HB, cur, K_ * W * 8);
    return popc(cur);
}
static el emul(el x, el y) { el z = { (x.a + (__int128)RP[x.j] * y.a) % M, (x.j + y.j) % K_ }; return z; }
/* a random hole of the last evaluation: side 0 = not reached from (e,A), 1 = from (e,B); returns 0 if none found */
static int hole(int side, el *u) {
    const u64 *H = side == 0 ? HA : HB;
    for (int tries = 0; tries < 64; tries++) {
        i64 j = rnd() % K_, w0 = rnd() % W;
        for (i64 w = w0, c = 0; c < W; c++, w = (w + 1) % W) {
            u64 v = ~H[j * W + w]; if (w == W - 1) v &= lastmask;
            if (v) { int b = __builtin_ctzll(v); u->a = w * 64 + b; u->j = j; return 1; }
        }
    }
    return 0;
}
/* targeted candidate for slot i: a word of length D-1 from e on `side` ending at hole u, with generator i at a random
 * position and the other letters random from S \ {s_i}; returns the generator value that makes the word end at u */
static el target(int i, int side, el u) {
    int L = D - 1, p = 1 + rnd() % L; el x = {0, 0}, z = {0, 0};
    for (int q = 1; q <= L; q++) {
        if (q == p) continue;
        int g; do g = rnd() % d; while (g == i);
        int useinv = (side == 0) ? (q & 1) : !(q & 1);
        el t = useinv ? SI[g] : S[g];
        if (q < p) x = emul(x, t); else z = emul(z, t);
    }
    el tp = emul(emul(inv(x), u), inv(z));        /* x tp z = u */
    int useinv = (side == 0) ? (p & 1) : !(p & 1);
    return useinv ? inv(tp) : tp;
}
static i64 cost(void) {
    for (int i = 0; i < d; i++) SI[i] = inv(S[i]);
    for (int g = 0; g < 2 * d; g++) { el t = g < d ? S[g] : SI[g - d]; JSH[g] = t.j;
        if (!ROT[g]) ROT[g] = malloc(sizeof(i64) * K_);
        for (i64 j = 0; j < K_; j++) ROT[g][j] = (RP[j] * t.a) % M; }
    if (D % 2 == 0) { lastA = N - ball(0); lastB = 0; return lastA; }
    lastA = N - ball(0); lastB = N - ball(1); return lastA + lastB;
}
static void writesol(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d %d meta %lld %lld %lld n 1 N %lld\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N);
    for (int i = 0; i < d; i++) fprintf(f, "%lld meta(a=%lld,j=%lld) z=0\n", (long long)(S[i].a * K_ + S[i].j), (long long)S[i].a, (long long)S[i].j);
    fclose(f);
}
static int readsol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0; char line[512]; if (!fgets(line, sizeof line, f)) return 0;
    int n = 0; long long a, j;
    while (n < d && fgets(line, sizeof line, f)) { char *p = strstr(line, "meta(a="); if (!p) continue;
        if (sscanf(p, "meta(a=%lld,j=%lld)", &a, &j) == 2) { S[n].a = a % M; S[n].j = j % K_; n++; } }
    fclose(f); return n == d;
}
static el rel(void) { el x; do { x.a = rnd() % M; x.j = rnd() % K_; } while (x.a == 0 && x.j == 0); return x; }
static int distinct(int i) { for (int t = 0; t < d; t++) if (t != i && S[t].a == S[i].a && S[t].j == S[i].j) return 0; return 1; }

/* ---------------- exhaustive mode (job raise-d10, director) ----------------
 * exh4 d D m k r [maxprint] : every S = {e, x, y, z} (d = 4) of G = Z_m x|_r Z_k up to the automorphisms
 * phi_{u,b}(a,j) = (u a + (1 - r^j) b, j) (u a unit mod m, b in Z_m; multipliers and conjugation by kernel elements).
 * x runs over orbit representatives of these automorphisms on G \ {e}, y over orbit representatives of (a subgroup
 * of) the stabiliser of x, z over all of G.  Cost as in hmeta (even D: B-side elements not within D-1 of (e,A)).
 * Prints the minimum cost, the number of cost-0 sets and writes the first cost-0 sets as hmeta solution files. */
static int *uf;
static int fnd(int x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static void uni(int a, int b) { a = fnd(a); b = fnd(b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }
static i64 idx(el x) { return x.a * K_ + x.j; }
static el phi(i64 u, i64 b, el x) { el y = { (i64)(((__int128)u * x.a + (__int128)((1 - RP[x.j] + M) % M) * b) % M), x.j }; return y; }
static i64 gcdl(i64 a, i64 b) { while (b) { i64 t = a % b; a = b; b = t; } return a; }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: exh4 d D m k r [maxprint]\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); M = atoll(argv[3]); K_ = atoll(argv[4]); R_ = atoll(argv[5]);
    int maxprint = argc > 6 ? atoi(argv[6]) : 5;
    if (d != 4) { fprintf(stderr, "d must be 4\n"); return 2; }
    if (mpow(R_, K_, M) != 1 % M) { fprintf(stderr, "r^k != 1 mod m\n"); return 2; }
    N = M * K_; RP = malloc(sizeof(i64) * K_); for (i64 j = 0; j < K_; j++) RP[j] = mpow(R_, j, M);
    W = (M + 63) / 64; W2 = (2 * M + 63) / 64 + 2; lastmask = (M % 64) ? ((1ULL << (M % 64)) - 1) : ~0ULL;
    HA = malloc(K_ * W * 8); HB = malloc(K_ * W * 8);
    SA = aligned_alloc(64, ((K_ * W * 8 + 63) / 64) * 64); SB = aligned_alloc(64, ((K_ * W * 8 + 63) / 64) * 64);
    DBL = aligned_alloc(64, ((K_ * W2 * 8 + 63) / 64) * 64);
    /* units mod m */
    i64 *U = malloc(sizeof(i64) * M); int nu = 0; for (i64 u = 1; u < M; u++) if (gcdl(u, M) == 1) U[nu++] = u;
    /* x representatives: orbits of the generators (u, 0) for all units u, and (1, 1) */
    uf = malloc(sizeof(int) * N);
    for (i64 i = 0; i < N; i++) uf[i] = (int)i;
    for (i64 i = 0; i < N; i++) { el x = { i / K_, i % K_ };
        for (int t = 0; t < nu; t++) uni((int)i, (int)idx(phi(U[t], 0, x)));
        uni((int)i, (int)idx(phi(1, 1, x))); }
    i64 *xr = malloc(sizeof(i64) * N); int nxr = 0;
    for (i64 i = 1; i < N; i++) if (fnd((int)i) == i) xr[nxr++] = i;
    /* orbit index of every element: x is taken from the lowest orbit among x, y, z, so y and z only need orbits >= x's */
    int *oid = malloc(sizeof(int) * N); { int *rk = malloc(sizeof(int) * N); for (int t = 0; t < nxr; t++) rk[xr[t]] = t;
        oid[0] = -1; for (i64 i = 1; i < N; i++) oid[i] = rk[fnd((int)i)]; free(rk); }
    fprintf(stderr, "G = Z%lld x|_%lld Z%lld, N = %lld, %d x-representatives\n", (long long)M, (long long)R_, (long long)K_, (long long)N, nxr);
    i64 best = 1 << 30, nzero = 0, nev = 0; double t0 = now();
    i64 *hist = calloc(64, sizeof(i64));
    i64 *yr = malloc(sizeof(i64) * N);
    for (int xi = 0; xi < nxr; xi++) {
        el x = { xr[xi] / K_, xr[xi] % K_ };
        /* stabiliser of x among phi_{u,b} */
        for (i64 i = 0; i < N; i++) uf[i] = (int)i;
        int nst = 0;
        for (int t = 0; t < nu; t++) for (i64 b = 0; b < M; b++) {
            el y = phi(U[t], b, x); if (y.a != x.a || y.j != x.j) continue;
            if (U[t] == 1 && b == 0) continue;
            nst++;
            for (i64 i = 0; i < N; i++) { el g = { i / K_, i % K_ }; uni((int)i, (int)idx(phi(U[t], b, g))); }
            if (nst >= 64) goto stabdone;   /* a generating subset is enough for correctness only if orbits stay exact;
                                              using fewer maps only makes orbits finer (more representatives), never wrong */
        }
        stabdone:;
        int nyr = 0; for (i64 i = 1; i < N; i++) if (i != xr[xi] && fnd((int)i) == i && oid[i] >= xi) yr[nyr++] = i;
        i64 bx = 1 << 30;
        for (int yi = 0; yi < nyr; yi++) {
            el y = { yr[yi] / K_, yr[yi] % K_ };
            for (i64 zi = 1; zi < N; zi++) {
                if (zi == xr[xi] || zi == yr[yi] || oid[zi] < xi) continue;
                el z = { zi / K_, zi % K_ };
                S[0] = (el){0, 0}; S[1] = x; S[2] = y; S[3] = z;
                i64 c = cost(); nev++;
                hist[c < 63 ? c : 63]++;
                if (c < bx) bx = c;
                if (c < best) best = c;
                if (c == 0) { nzero++;
                    if (nzero <= maxprint) { char fn[256]; snprintf(fn, sizeof fn, "exh4_d%dD%d_m%lld_k%lld_r%lld_%lld.sol", d, D, (long long)M, (long long)K_, (long long)R_, (long long)nzero); writesol(fn);
                        printf("COST0 %s x=(%lld,%lld) y=(%lld,%lld) z=(%lld,%lld)\n", fn, (long long)x.a, (long long)x.j, (long long)y.a, (long long)y.j, (long long)z.a, (long long)z.j); fflush(stdout); } }
            }
        }
        fprintf(stderr, "x %d/%d (%lld,%lld): stab maps %d, y reps %d, min cost %lld (all so far %lld, zero %lld, evals %lld, %.0fs)\n",
                xi + 1, nxr, (long long)x.a, (long long)x.j, nst, nyr, (long long)bx, (long long)best, (long long)nzero, (long long)nev, now() - t0);
    }
    printf("EXH4 d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld evals=%lld min=%lld zero=%lld time=%.1f hist0-5=%lld,%lld,%lld,%lld,%lld,%lld\n",
           d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)(2 * N), (long long)nev, (long long)best, (long long)nzero, now() - t0,
           (long long)hist[0], (long long)hist[1], (long long)hist[2], (long long)hist[3], (long long)hist[4], (long long)hist[5]);
    return 0;
}
