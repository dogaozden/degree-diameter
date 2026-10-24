/* pslcheck_b1.c -- card B1 of squad d11D10-r1: independent low-memory checker for Haar graphs
 * H(G,S), G = PSL(2,p) x Z_n, |S| = d, written from scratch (own element encoding, own BFS).
 *
 * Input: header "d D psl p n NCYC N NTOT", then d lines "<idx> mat(a,b,c,d) z=Z" (either sign allowed).
 * Graph: vertices (g,A), (g,B); edges (g,A) ~ (s g,B) for s in S, so (g,B) ~ (s^-1 g,A).
 * Right multiplication is an automorphism that is transitive on each side, so
 *   diameter = max(ecc(e,A), ecc(e,B)),  VALID iff connected and both eccentricities <= D.
 *
 * Own encoding of PSL(2,p): the canonical matrix has sign chosen so that the first nonzero entry of
 * (a,b,c,d) lies in 1..h, h = (p-1)/2.  Index (0 = identity):
 *   a != 0 :  idx = (a-1) p^2 + b p + c,            d = (1+bc)/a
 *   a == 0 :  idx = h p^2 + (b-1) p + d,            b in 1..h, c = -1/b
 * BFS: every PSL index carries a block of n bits (bit z = "(i,z) reached"), stored in W = ceil(n/64)
 * words. Left translation by s = (M,z0) sends block i to block T_M(i) and rotates its bits by z0 mod n.
 * Level step: newB = OR_s L_s(frontierA) and newA = OR_s L_{s^-1}(frontierB), minus visited.
 * Exit status 0 = VALID, 1 = INVALID (or unreadable input), 2 = internal error.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

typedef unsigned long long u64;

static int p, h, n, d, D, W;
static u64 NPSL, NTOT;
static int *ea, *eb, *ec, *ed;   /* decoded matrix of every PSL index */
static int *invt;
static unsigned int **Tf, **Tb;  /* Tf[k][i] = idx(M_k X_i), Tb[k][i] = idx(M_k^-1 X_i) */
static int *rf, *rb;             /* z-rotations: forward z_k, backward (n - z_k) mod n */
static u64 maskTop;              /* bits of the top word that are inside the n-bit block */
static u64 *cur[2], *nxt[2], *vis[2];

static int imod(long long x) { x %= p; if (x < 0) x += p; return (int)x; }

static int ispr(long long x) {
    if (x < 2) return 0;
    for (long long t = 2; t * t <= x; t++) if (x % t == 0) return 0;
    return 1;
}

static int powmod(int b, int e) {
    long long r = 1, x = b % p;
    while (e) { if (e & 1) r = r * x % p; x = x * x % p; e >>= 1; }
    return (int)r;
}

static u64 canon_index(int a, int b, int c, int dd) {
    if (a != 0) {
        if (a > h) { a = (p - a) % p; b = (p - b) % p; c = (p - c) % p; dd = (p - dd) % p; }
        return (u64)(a - 1) * p * p + (u64)b * p + (u64)c;
    }
    if (b > h) { b = (p - b) % p; c = (p - c) % p; dd = (p - dd) % p; }
    return (u64)h * p * p + (u64)(b - 1) * p + (u64)dd;
}

static void decode(u64 i, int *a, int *b, int *c, int *dd) {
    u64 H0 = (u64)h * p * p;
    if (i < H0) {
        int A = (int)(i / ((u64)p * p)) + 1;
        int B = (int)((i / p) % p);
        int C = (int)(i % p);
        *a = A; *b = B; *c = C;
        *dd = (int)((1 + (long long)B * C) % p * invt[A] % p);
    } else {
        u64 j = i - H0;
        int B = (int)(j / p) + 1;
        *a = 0; *b = B; *dd = (int)(j % p);
        *c = (p - invt[B]) % p;
    }
}

/* ---- rotation-or of an n-bit block: dst |= rot(src, r), bit z -> (z + r) mod n ---- */
static u64 *TL, *TR;             /* temporaries for W > 1 */

static void shl_words(u64 *out, const u64 *in, int s) {
    int q = s >> 6, t = s & 63;
    for (int j = 0; j < W; j++) {
        int src = j - q; u64 v = 0;
        if (src >= 0) {
            v = in[src] << t;
            if (t && src >= 1) v |= in[src - 1] >> (64 - t);
        }
        out[j] = v;
    }
}

static void shr_words(u64 *out, const u64 *in, int s) {
    int q = s >> 6, t = s & 63;
    for (int j = 0; j < W; j++) {
        int src = j + q; u64 v = 0;
        if (src < W) {
            v = in[src] >> t;
            if (t && src + 1 < W) v |= in[src + 1] << (64 - t);
        }
        out[j] = v;
    }
}

static inline void rot_or1(u64 *dst, u64 x, int r) {       /* W == 1 */
    if (r == 0) { *dst |= x; return; }
    *dst |= ((x << r) | (x >> (n - r))) & maskTop;
}

static void rot_orW(u64 *dst, const u64 *src, int r) {     /* W > 1 */
    if (r == 0) { for (int j = 0; j < W; j++) dst[j] |= src[j]; return; }
    shl_words(TL, src, r);
    shr_words(TR, src, n - r);
    for (int j = 0; j < W; j++) {
        u64 v = TL[j] | TR[j];
        if (j == W - 1) v &= maskTop;
        dst[j] |= v;
    }
}

/* one BFS level: nB = OR_k L_k(cA), nA = OR_k L_k^-1(cB); no visited masking here */
static void step(u64 *cA, u64 *cB, u64 *nA, u64 *nB) {
    size_t words = (size_t)NPSL * W;
    memset(nA, 0, words * sizeof(u64));
    memset(nB, 0, words * sizeof(u64));
    for (int k = 0; k < d; k++) {
        const unsigned int *tf = Tf[k], *tb = Tb[k];
        if (W == 1) {
            for (u64 i = 0; i < NPSL; i++) { u64 x = cA[i]; if (x) rot_or1(&nB[tf[i]], x, rf[k]); }
            for (u64 i = 0; i < NPSL; i++) { u64 x = cB[i]; if (x) rot_or1(&nA[tb[i]], x, rb[k]); }
        } else {
            for (u64 i = 0; i < NPSL; i++) {
                const u64 *s = cA + i * W; int any = 0;
                for (int j = 0; j < W; j++) any |= (s[j] != 0);
                if (any) rot_orW(nB + (u64)tf[i] * W, s, rf[k]);
            }
            for (u64 i = 0; i < NPSL; i++) {
                const u64 *s = cB + i * W; int any = 0;
                for (int j = 0; j < W; j++) any |= (s[j] != 0);
                if (any) rot_orW(nA + (u64)tb[i] * W, s, rb[k]);
            }
        }
    }
}

/* BFS from (e,side); fills eccentricity and number of reached vertices (both sides) */
static void run_bfs(int side, int *ecc, u64 *reached) {
    size_t words = (size_t)NPSL * W;
    memset(cur[0], 0, words * sizeof(u64)); memset(cur[1], 0, words * sizeof(u64));
    memset(vis[0], 0, words * sizeof(u64)); memset(vis[1], 0, words * sizeof(u64));
    cur[side][0] = 1; vis[side][0] = 1;   /* identity: PSL index 0, z = 0 */
    u64 total = 1; int lev = 0;
    for (;;) {
        step(cur[0], cur[1], nxt[0], nxt[1]);
        u64 newc = 0;
        for (size_t t = 0; t < words; t++) {
            u64 a = nxt[0][t] & ~vis[0][t];
            u64 b = nxt[1][t] & ~vis[1][t];
            nxt[0][t] = a; nxt[1][t] = b;
            vis[0][t] |= a; vis[1][t] |= b;
            newc += __builtin_popcountll(a) + __builtin_popcountll(b);
        }
        if (newc == 0) break;
        lev++; total += newc;
        u64 *tmp;
        tmp = cur[0]; cur[0] = nxt[0]; nxt[0] = tmp;
        tmp = cur[1]; cur[1] = nxt[1]; nxt[1] = tmp;
    }
    *ecc = lev; *reached = total;
}

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: %s FILE\n", argv[0]); return 2; }
    clock_t t0 = clock();
    FILE *f = fopen(argv[1], "r");
    if (!f) { printf("INVALID reason=cannot open %s\n", argv[1]); return 1; }
    static char line[8192];
    if (!fgets(line, sizeof line, f)) { printf("INVALID reason=empty file\n"); return 1; }
    char fam[32] = {0};
    long long pp = 0, nn = 0, NT = 0; int dh = 0, Dh = 0;
    if (sscanf(line, "%d %d %31s %lld n %lld N %lld", &dh, &Dh, fam, &pp, &nn, &NT) != 6 ||
        strcmp(fam, "psl") != 0) {
        printf("INVALID reason=header is not 'd D psl p n NCYC N NTOT'\n"); return 1;
    }
    d = dh; D = Dh; p = (int)pp; n = (int)nn;
    if (d < 1 || D < 1 || n < 1 || p < 3 || (p & 1) == 0 || p > 100000 || !ispr(p)) {
        printf("INVALID reason=bad parameters p=%lld n=%lld\n", pp, nn); return 1;
    }
    h = (p - 1) / 2;
    NPSL = (u64)h * (u64)p * (u64)(p + 1);        /* |PSL(2,p)| = p(p^2-1)/2 */
    NTOT = NPSL * (u64)n;
    if ((u64)NT != NTOT) { printf("INVALID reason=header N=%lld but |PSL|*n=%llu\n", NT, NTOT); return 1; }
    if (NPSL >= (1ULL << 32)) { printf("INVALID reason=group too large for this checker\n"); return 2; }
    W = (n + 63) / 64;
    { int tb = n - 64 * (W - 1); maskTop = (tb == 64) ? ~0ULL : ((1ULL << tb) - 1); }
    invt = malloc(sizeof(int) * (size_t)p);
    for (int x = 1; x < p; x++) invt[x] = powmod(x, p - 2);

    /* ---- read generators ---- */
    int (*gm)[4] = malloc(sizeof(int[4]) * (size_t)d);
    int *gz = malloc(sizeof(int) * (size_t)d);
    u64 *seen = calloc((size_t)(NTOT / 64 + 1), sizeof(u64));
    if (!gm || !gz || !seen) { printf("INVALID reason=out of memory\n"); return 2; }
    int cnt = 0;
    while (fgets(line, sizeof line, f)) {
        char *q = strstr(line, "mat(");
        if (!q) continue;
        long long A, B, C, Dm, Z;
        if (sscanf(q, "mat(%lld,%lld,%lld,%lld) z=%lld", &A, &B, &C, &Dm, &Z) != 5) {
            printf("INVALID reason=cannot parse generator line %d\n", cnt + 1); return 1;
        }
        if (cnt >= d) { printf("INVALID reason=more than d=%d generator lines\n", d); return 1; }
        int a = imod(A), b = imod(B), c = imod(C), dd = imod(Dm);
        if (imod((long long)a * dd - (long long)b * c) != 1) {
            printf("INVALID reason=generator %d has det != 1 mod p\n", cnt + 1); return 1;
        }
        if (Z < 0 || Z >= n) { printf("INVALID reason=generator %d has z=%lld outside 0..n-1\n", cnt + 1, Z); return 1; }
        u64 idx = canon_index(a, b, c, dd);
        u64 key = idx * (u64)n + (u64)Z;
        if ((seen[key >> 6] >> (key & 63)) & 1ULL) {
            printf("INVALID reason=generator %d repeats an earlier generator (not distinct in PSL x Z_n)\n", cnt + 1);
            return 1;
        }
        seen[key >> 6] |= 1ULL << (key & 63);
        gm[cnt][0] = a; gm[cnt][1] = b; gm[cnt][2] = c; gm[cnt][3] = dd;
        gz[cnt] = (int)Z;
        cnt++;
    }
    fclose(f);
    if (cnt != d) { printf("INVALID reason=%d generator lines, header says d=%d\n", cnt, d); return 1; }

    /* ---- decode table and self-test of the encoding ---- */
    ea = malloc(sizeof(int) * NPSL); eb = malloc(sizeof(int) * NPSL);
    ec = malloc(sizeof(int) * NPSL); ed = malloc(sizeof(int) * NPSL);
    if (!ea || !eb || !ec || !ed) { printf("INVALID reason=out of memory\n"); return 2; }
    for (u64 i = 0; i < NPSL; i++) {
        int a, b, c, dd;
        decode(i, &a, &b, &c, &dd);
        if (imod((long long)a * dd - (long long)b * c) != 1 || canon_index(a, b, c, dd) != i) {
            printf("INTERNAL self-test failed at index %llu\n", i); return 2;
        }
        ea[i] = a; eb[i] = b; ec[i] = c; ed[i] = dd;
    }

    /* ---- translation tables ---- */
    Tf = malloc(sizeof(unsigned int *) * (size_t)d); Tb = malloc(sizeof(unsigned int *) * (size_t)d);
    rf = malloc(sizeof(int) * (size_t)d); rb = malloc(sizeof(int) * (size_t)d);
    if (!Tf || !Tb || !rf || !rb) { printf("INVALID reason=out of memory\n"); return 2; }
    for (int k = 0; k < d; k++) {
        Tf[k] = malloc(sizeof(unsigned int) * NPSL); Tb[k] = malloc(sizeof(unsigned int) * NPSL);
        if (!Tf[k] || !Tb[k]) { printf("INVALID reason=out of memory\n"); return 2; }
        long long ma = gm[k][0], mb = gm[k][1], mc = gm[k][2], mdd = gm[k][3];
        long long ia = mdd, ib = imod(-mb), ic = imod(-mc), id = ma;   /* inverse of M_k */
        for (u64 i = 0; i < NPSL; i++) {
            long long a2 = ea[i], b2 = eb[i], c2 = ec[i], d2 = ed[i];
            Tf[k][i] = (unsigned int)canon_index(imod(ma * a2 + mb * c2), imod(ma * b2 + mb * d2),
                                                 imod(mc * a2 + mdd * c2), imod(mc * b2 + mdd * d2));
            Tb[k][i] = (unsigned int)canon_index(imod(ia * a2 + ib * c2), imod(ia * b2 + ib * d2),
                                                 imod(ic * a2 + id * c2), imod(ic * b2 + id * d2));
        }
        for (u64 i = 0; i < NPSL; i++)
            if (Tb[k][Tf[k][i]] != i) { printf("INTERNAL inverse-table self-test failed (k=%d)\n", k); return 2; }
        rf[k] = gz[k];
        rb[k] = (n - gz[k]) % n;
    }
    printf("group=psl %d x Z_%d |PSL|=%llu |G|=%llu vertices=%llu W=%d d=%d tables_s=%.2f\n",
           p, n, NPSL, NTOT, 2 * NTOT, W, d, (double)(clock() - t0) / CLOCKS_PER_SEC);
    fflush(stdout);

    /* ---- BFS storage ---- */
    size_t words = (size_t)NPSL * W;
    for (int s = 0; s < 2; s++) {
        cur[s] = calloc(words, sizeof(u64)); nxt[s] = calloc(words, sizeof(u64)); vis[s] = calloc(words, sizeof(u64));
        if (!cur[s] || !nxt[s] || !vis[s]) { printf("INVALID reason=out of memory\n"); return 2; }
    }
    TL = calloc((size_t)W, sizeof(u64)); TR = calloc((size_t)W, sizeof(u64));

    int eA = -1, eB = -1; u64 rA = 0, rB = 0;
    clock_t t1 = clock();
    run_bfs(0, &eA, &rA);
    printf("bfs from (e,A): ecc=%d reached=%llu of %llu (%.2f s)\n", eA, rA, 2 * NTOT,
           (double)(clock() - t1) / CLOCKS_PER_SEC);
    fflush(stdout);
    t1 = clock();
    run_bfs(1, &eB, &rB);
    printf("bfs from (e,B): ecc=%d reached=%llu of %llu (%.2f s)\n", eB, rB, 2 * NTOT,
           (double)(clock() - t1) / CLOCKS_PER_SEC);

    u64 V = 2 * NTOT;
    if (rA != V || rB != V) {
        printf("INVALID d=%d D=%d vertices=%llu reason=disconnected eccA=%s eccB=%s\n", d, D, V,
               rA == V ? "finite" : "inf", rB == V ? "finite" : "inf");
        return 1;
    }
    if (eA > D || eB > D) {
        printf("INVALID d=%d D=%d vertices=%llu reason=diameter exceeds D eccA=%d eccB=%d\n", d, D, V, eA, eB);
        return 1;
    }
    printf("VALID d=%d D=%d vertices=%llu eccA=%d eccB=%d\n", d, D, V, eA, eB);
    return 0;
}
