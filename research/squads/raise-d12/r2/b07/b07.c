/* b07 (raise-d12 r2): Haar graphs H(G,S) for G = SL(2,32) x H, H = Z_191 x|_r Z_5 (order 955).
   alpha = (x -> x^2 on GF(32), order 5) x beta, beta(a,j) = (u a, j), u = r^UEXP (order 5).
   S = {e, f, o0..o4}: f alpha-fixed (order 3 in SL(2,2) x {0} by default), o_i = alpha^i(s), s random.
   Delta = 7, N = 31,262,880, 2N vertices, target diameter 12 (need unreached = 0 from (e,A) and (e,B)).
   Usage: b07 secs seed OUTFILE [INITFILE]    env: UEXP (1..4), FIDX (index in Fix list, -1 = first order-3)
   Cost = #A-vertices at dist > 12 + #B-vertices at dist > 12 from (e,A) (horizon 12 expansions).
   Memory: 4 bitsets of N bits (16 MB) + 2 MB index table + small tables.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#ifdef DIH
#define HN 922          /* dihedral D_461, element h = a*2 + (0 for +1, 1 for -1) */
#define HP 461
#define HA(h) ((h) / 2)
#define HB(h) ((h) % 2)
#else
#define HN 955          /* Z_191 x|_r Z_5, element h = a*5 + j */
#define HP 191
#define HA(h) ((h) / 5)
#define HB(h) ((h) % 5)
#endif
#define NSL 32736
#define NG ((size_t)NSL * HN)
#define WORDS ((NG + 63) / 64)
#define D 12

static uint8_t gfm[32][32];
static uint8_t Mx[NSL][4];
static uint16_t *idxOf;      /* 1<<20 entries */
static uint16_t Hmul[HN][HN];
static uint16_t Hinv[HN];
static uint16_t phiSL[NSL], betaH[HN];
static int rp[5];
static uint32_t eSL;
static uint64_t *visA, *visB, *cur, *nxt;
static uint16_t SLp[14][NSL];
static uint16_t Hp[14][HN];
static uint64_t cntA, cntB;

typedef struct { uint16_t s, h; } Gel;

static int key4(int a, int b, int c, int d) { return (a << 15) | (b << 10) | (c << 5) | d; }

static void gf_init(void) {
    for (int a = 0; a < 32; a++)
        for (int b = 0; b < 32; b++) {
            int r = 0, aa = a, bb = b;
            for (int i = 0; i < 5; i++) {
                if (bb & 1) r ^= aa;
                bb >>= 1;
                aa <<= 1;
                if (aa & 32) aa ^= 0x25; /* x^5 + x^2 + 1 */
            }
            gfm[a][b] = (uint8_t)r;
        }
}

static uint16_t slmul(uint16_t i, uint16_t j) {
    const uint8_t *A = Mx[i], *B = Mx[j];
    int a = gfm[A[0]][B[0]] ^ gfm[A[1]][B[2]];
    int b = gfm[A[0]][B[1]] ^ gfm[A[1]][B[3]];
    int c = gfm[A[2]][B[0]] ^ gfm[A[3]][B[2]];
    int d = gfm[A[2]][B[1]] ^ gfm[A[3]][B[3]];
    return idxOf[key4(a, b, c, d)];
}

static uint16_t slinv(uint16_t i) { /* det 1, char 2: inverse = [[d,b],[c,a]] */
    const uint8_t *A = Mx[i];
    return idxOf[key4(A[3], A[1], A[2], A[0])];
}

static uint16_t Hm(int h1, int h2) { return Hmul[h1][h2]; }

static uint32_t gidx(Gel g) { return (uint32_t)g.s * HN + g.h; }

static Gel gelof(uint32_t x) { Gel g; g.s = (uint16_t)(x / HN); g.h = (uint16_t)(x % HN); return g; }

static Gel alpha(Gel g) { Gel r; r.s = phiSL[g.s]; r.h = betaH[g.h]; return r; }

static Gel ginv(Gel g) { Gel r; r.s = slinv(g.s); r.h = Hinv[g.h]; return r; }

static void setup_tables(int uexp) {
    gf_init();
    idxOf = malloc(sizeof(uint16_t) << 20);
    memset(idxOf, 0xFF, sizeof(uint16_t) << 20);
    int n = 0;
    for (int a = 0; a < 32; a++)
        for (int b = 0; b < 32; b++)
            for (int c = 0; c < 32; c++)
                for (int d = 0; d < 32; d++)
                    if ((gfm[a][d] ^ gfm[b][c]) == 1) {
                        if (n >= NSL) { fprintf(stderr, "SL overflow\n"); exit(1); }
                        Mx[n][0] = a; Mx[n][1] = b; Mx[n][2] = c; Mx[n][3] = d;
                        idxOf[key4(a, b, c, d)] = n;
                        n++;
                    }
    if (n != NSL) { fprintf(stderr, "SL size %d\n", n); exit(1); }
    eSL = idxOf[key4(1, 0, 0, 1)];
    for (int i = 0; i < NSL; i++) {
        int a = Mx[i][0], b = Mx[i][1], c = Mx[i][2], d = Mx[i][3];
        phiSL[i] = idxOf[key4(gfm[a][a], gfm[b][b], gfm[c][c], gfm[d][d])];
    }
#ifdef DIH
    int r = 0;
    for (int t = 2; t < HP; t++) { int x = 1; for (int k = 0; k < 92; k++) x = x * t % HP; if (x != 1) { r = x; break; } }
    if (r == 0 || (r * r % HP * r % HP * r % HP * r % HP) != 1) { fprintf(stderr, "u order\n"); exit(1); }
    for (int h1 = 0; h1 < HN; h1++)
        for (int h2 = 0; h2 < HN; h2++) {
            int a1 = h1 / 2, s1 = h1 % 2, a2 = h2 / 2, s2 = h2 % 2;
            int a = s1 ? (a1 - a2 + HP) % HP : (a1 + a2) % HP;
            Hmul[h1][h2] = (uint16_t)(a * 2 + (s1 ^ s2));
        }
    for (int h1 = 0; h1 < HN; h1++)
        for (int h2 = 0; h2 < HN; h2++)
            if (Hmul[h1][h2] == 0) { Hinv[h1] = (uint16_t)h2; break; }
    int u = r;
    for (int h = 0; h < HN; h++) betaH[h] = (uint16_t)((u * (h / 2) % HP) * 2 + h % 2);
#else
    /* H = Z_191 x|_r Z_5 */
    int r = 0;
    for (int t = 2; t < HP; t++) {
        int x = 1;
        for (int k = 0; k < 38; k++) x = x * t % HP;
        if (x != 1) { r = x; break; }
    }
    rp[0] = 1;
    for (int j = 1; j < 5; j++) rp[j] = rp[j - 1] * r % HP;
    if (rp[4] * r % HP != 1) { fprintf(stderr, "r order\n"); exit(1); }
    for (int h1 = 0; h1 < HN; h1++)
        for (int h2 = 0; h2 < HN; h2++) {
            int a1 = h1 / 5, j1 = h1 % 5, a2 = h2 / 5, j2 = h2 % 5;
            int a = (a1 + rp[j1] * a2) % HP;
            int j = (j1 + j2) % 5;
            Hmul[h1][h2] = (uint16_t)(a * 5 + j);
        }
    for (int h1 = 0; h1 < HN; h1++)
        for (int h2 = 0; h2 < HN; h2++)
            if (Hmul[h1][h2] == 0) { Hinv[h1] = (uint16_t)h2; break; }
    int u = rp[uexp];
    for (int h = 0; h < HN; h++) {
        int a = h / 5, j = h % 5;
        betaH[h] = (uint16_t)((u * a % HP) * 5 + j);
    }
#endif
}

static void setperm(int k, Gel s) {
    for (int i = 0; i < NSL; i++) SLp[k][i] = slmul(s.s, (uint16_t)i);
    for (int h = 0; h < HN; h++) Hp[k][h] = Hm(s.h, h);
}

static int bit(const uint64_t *b, uint32_t x) { return (b[x >> 6] >> (x & 63)) & 1; }

/* BFS with `D` expansions from (x0, side). Returns nothing; sets cntA, cntB (visited counts). */
static void bfs(int side, uint32_t x0) {
    memset(visA, 0, WORDS * 8);
    memset(visB, 0, WORDS * 8);
    memset(cur, 0, WORDS * 8);
    uint64_t *v0 = side == 0 ? visA : visB;
    v0[x0 >> 6] |= 1ULL << (x0 & 63);
    cur[x0 >> 6] |= 1ULL << (x0 & 63);
    cntA = side == 0;
    cntB = side == 1;
    int cs = side;
    for (int t = 0; t < D; t++) {
        memset(nxt, 0, WORDS * 8);
        uint64_t newc = 0;
        uint64_t *vis = cs == 0 ? visB : visA;
        int k0 = cs == 0 ? 0 : 7;
        for (size_t w = 0; w < WORDS; w++) {
            uint64_t bits = cur[w];
            while (bits) {
                int b = __builtin_ctzll(bits);
                bits &= bits - 1;
                uint32_t x = (uint32_t)(w * 64 + b);
                uint32_t xs = x / HN, xh = x % HN;
                for (int k = k0; k < k0 + 7; k++) {
                    uint32_t y = (uint32_t)SLp[k][xs] * HN + Hp[k][xh];
                    uint64_t m = 1ULL << (y & 63);
                    if (!(vis[y >> 6] & m)) {
                        vis[y >> 6] |= m;
                        nxt[y >> 6] |= m;
                        newc++;
                    }
                }
            }
        }
        if (newc == 0) break;
        if (getenv("DIAG")) fprintf(stderr, "  level %d side %d new %llu\n", t + 1, cs, (unsigned long long)newc);
        if (cs == 0) cntB += newc; else cntA += newc;
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
        cs ^= 1;
    }
}

/* S = Sg[0..6]; perms k=0..6 are left mult by Sg[k], k=7..13 by inverses */
static uint64_t evaluate(const Gel *Sg, uint64_t *unB_out) {
    for (int k = 0; k < 7; k++) {
        setperm(k, Sg[k]);
        setperm(k + 7, ginv(Sg[k]));
    }
    bfs(0, (uint32_t)(eSL * HN));
    uint64_t unA = NG - cntA, unB = NG - cntB;
    if (unB_out) *unB_out = unB;
    return unA + unB;
}

static uint64_t rng_s = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17;
    return rng_s * 0x2545F4914F6CDD1DULL;
}

static int cmpu(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    return (x > y) - (x < y);
}

static double now(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void write_sol(const char *fn, const Gel *Sg, uint64_t cost, int uexp, int fidx) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    fprintf(f, "# b07 G=SL(2,32) x H, H=Z191 x|_r Z5, u=r^%d, Delta=7, cost=%llu, D=12\n", uexp, (unsigned long long)cost);
    fprintf(f, "# element: SL matrix a b c d (GF(32) as 5-bit ints, poly x^5+x^2+1), H element a j (r = rp[1])\n");
    fprintf(f, "# S order: e, f(fixed), o0..o4 (alpha orbit). fidx=%d\n", fidx);
    for (int k = 0; k < 7; k++) {
        int i = Sg[k].s;
        fprintf(f, "%d %d %d %d %d %d\n", Mx[i][0], Mx[i][1], Mx[i][2], Mx[i][3], HA(Sg[k].h), HB(Sg[k].h));
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: b07 secs seed OUT\n"); return 1; }
    double secs = atof(argv[1]);
    rng_s ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    const char *out = argv[3];
    int uexp = getenv("UEXP") ? atoi(getenv("UEXP")) : 1;
    int fidxenv = getenv("FIDX") ? atoi(getenv("FIDX")) : -1;
    int maxs = 400000;

    setup_tables(uexp);
    visA = malloc(WORDS * 8); visB = malloc(WORDS * 8);
    cur = malloc(WORDS * 8); nxt = malloc(WORDS * 8);
    if (!visA || !visB || !cur || !nxt) { fprintf(stderr, "alloc\n"); return 1; }

    /* Fix(alpha) \ {e} */
    Gel fixed[64]; int nfix = 0;
    for (uint16_t i = 0; i < NSL; i++) {
        if (phiSL[i] != i) continue;
        for (uint16_t h = 0; h < HN; h++) {
            if (betaH[h] != h) continue;
            if (i == eSL && h == 0) continue;
            Gel g; g.s = i; g.h = h; fixed[nfix++] = g;
        }
    }
    /* default f: first element with f^3 = e (order 3) */
    Gel f = fixed[0];
    int fidx = -1;
    if (getenv("FHIDX")) {
        int fh = atoi(getenv("FHIDX")), fso = getenv("FSORD") ? atoi(getenv("FSORD")) : 3;
        for (int q = 0; q < nfix; q++) {
            if (fixed[q].h != fh) continue;
            Gel g = fixed[q], p = g; /* p = g^fso in SL part, H part fixed-point */
            for (int k = 1; k < fso; k++) p.s = slmul(p.s, g.s);
            if ((fso == 0) ? (g.s == eSL) : (g.s != eSL && p.s == eSL)) { f = g; fidx = q; break; }
        }
    }
    else if (fidxenv >= 0 && fidxenv < nfix) { f = fixed[fidxenv]; fidx = fidxenv; }
    else {
        for (int q = 0; q < nfix; q++) {
            Gel g = fixed[q];
            uint16_t s3 = slmul(slmul(g.s, g.s), g.s);
            uint16_t h3 = Hm(Hm(g.h, g.h), g.h);
            if (s3 == eSL && h3 == 0) { f = g; fidx = q; break; }
        }
    }
    fprintf(stderr, "nfix=%d f=(s=%u,h=%u) fidx=%d uexp=%d\n", nfix, f.s, f.h, fidx, uexp);

    if (getenv("RANDS")) {
        /* diagnostic: 7 uniformly random elements of G (no orbit structure) */
        Gel R[7];
        for (int k = 0; k < 7; k++) { R[k].s = (uint16_t)(rnd() % NSL); R[k].h = (uint16_t)(rnd() % HN); }
        R[0].s = eSL; R[0].h = 0;
        uint64_t unB;
        uint64_t c = evaluate(R, &unB);
        for (int k = 0; k < 7; k++) printf("H-part %d: a=%d sign=%d sl=%d\n", k, HA(R[k].h), HB(R[k].h), R[k].s);
        printf("random S cost %llu unB %llu\n", (unsigned long long)c, (unsigned long long)unB);
        return 0;
    }
    double t0 = now();
    uint64_t best = (uint64_t)-1;
    uint32_t *costs = malloc(sizeof(uint32_t) * maxs);
    int ns = 0;
    long nsamp = 0;
    Gel Sg[7];
    while (now() - t0 < secs) {
        Gel s; s.s = (uint16_t)(rnd() % NSL); s.h = (uint16_t)(rnd() % HN);
        Gel o[5]; o[0] = s;
        for (int i = 1; i < 5; i++) o[i] = alpha(o[i - 1]);
        if (o[1].s == s.s && o[1].h == s.h) continue; /* alpha-fixed: orbit size 1 */
        Gel e; e.s = (uint16_t)eSL; e.h = 0;
        Sg[0] = e; Sg[1] = f;
        for (int i = 0; i < 5; i++) Sg[2 + i] = o[i];
        /* distinctness check of S */
        int ok = 1;
        for (int a = 0; a < 7 && ok; a++) for (int b = a + 1; b < 7; b++)
            if (Sg[a].s == Sg[b].s && Sg[a].h == Sg[b].h) { ok = 0; break; }
        if (!ok) continue;
        uint64_t unB;
        uint64_t c = evaluate(Sg, &unB);
        nsamp++;
        if (ns < maxs) costs[ns++] = (uint32_t)c;
        if (c < best) {
            best = c;
            fprintf(stderr, "t=%.1f sample %ld new best cost %llu (unB %llu)\n", now() - t0, nsamp,
                    (unsigned long long)c, (unsigned long long)unB);
            write_sol(out, Sg, c, uexp, fidx);
        }
        if (c == 0) {
            bfs(1, (uint32_t)(eSL * HN));
            uint64_t unB2 = (NG - cntA) + (NG - cntB);
            fprintf(stderr, "COST0 from (e,A); check from (e,B): cost %llu\n", (unsigned long long)unB2);
            if (unB2 == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s.VALID", out);
                write_sol(fn, Sg, 0, uexp, fidx);
                fprintf(stderr, "VALID diameter<=12 written to %s\n", fn);
                break;
            }
        }
    }
    /* stats */
    double tt = now() - t0;
    /* sort costs (simple) */
    qsort(costs, ns, sizeof(uint32_t), cmpu);
    printf("samples=%ld time=%.1fs per_eval=%.2fs best=%llu\n", nsamp, tt, nsamp ? tt / nsamp : 0.0, (unsigned long long)best);
    if (ns) printf("cost quantiles: min=%u p1=%u p10=%u median=%u\n", costs[0], costs[ns / 100], costs[ns / 10], costs[ns / 2]);
    printf("lowest costs:");
    for (int i = 0; i < ns && i < 25; i++) printf(" %u", costs[i]);
    printf("\n");
    return 0;
}

