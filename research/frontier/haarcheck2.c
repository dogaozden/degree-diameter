/*
 * haarcheck2.c
 *
 * Independent low-memory diameter checker for Haar graphs H(G, S),
 * G = SL(2,p) x Z_n, read from a solution file.
 *
 * Solution file:
 *   line 1:  d D sl p n NCYC N NTOT
 *   next d:  <index> mat(a,b,c,d) z=<k>
 *
 * Graph: vertices (g,A) and (g,B), g in G. (g,A) ~ (s g,B) for s in S.
 * G acts by right multiplication, so the diameter is <= D exactly when BFS
 * from (e,A) and BFS from (e,B) each reach every vertex within D steps.
 *
 * Memory: four bitsets over G (visA, visB, cur, next), about 4 bits per
 * element. Group elements are indexed as sl * n + k, where sl is a
 * bijective index of SL(2,p):
 *   a != 0:  sl = (a-1) p^2 + b p + c           (d is determined by a,b,c)
 *   a == 0:  sl = (p-1) p^2 + (b-1) p + d       (c = -1/b)
 *
 * Build:  cc -O3 -o haarcheck2 haarcheck2.c
 * Run:    ./haarcheck2 <solution-file>
 */

#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint32_t u32;
typedef uint64_t u64;

typedef struct {
    u32 a, b, c, d;
} Mat;

typedef struct {
    Mat m;   /* generator s = (m, k)     */
    u32 k;
    Mat mi;  /* inverse s^-1 = (mi, ki)  */
    u32 ki;
} Gen;

static u32 P, NC;
static u64 PP, FIRST;   /* PP = p^2, FIRST = (p-1) p^2 = count of a != 0 indices */
static u64 NSL, NG;     /* |SL(2,p)| = p(p^2-1), |G| = NSL * n */
static u32 *INV;        /* INV[x] = x^-1 mod p */
static u64 FM_M;        /* Lemire fastmod constant for divisor P */

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* x mod P for 32-bit x (Lemire, Kaser, Kurz 2019). Checked against % at startup. */
static inline u32 mod_p(u32 x) {
    u64 low = FM_M * (u64)x;
    return (u32)(((__uint128_t)low * P) >> 64);
}

static u64 powmod(u64 b, u64 e, u64 m) {
    u64 r = 1;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void setup(u32 p, u32 n) {
    P = p;
    NC = n;
    FM_M = UINT64_C(0xFFFFFFFFFFFFFFFF) / P + 1;
    PP = (u64)P * P;
    FIRST = (u64)(P - 1) * PP;
    NSL = (u64)P * (PP - 1);
    NG = NSL * NC;
    INV = malloc(sizeof(u32) * P);
    INV[0] = 0;
    for (u32 x = 1; x < P; x++) INV[x] = (u32)powmod(x, P - 2, P);
}

static inline Mat decode_sl(u64 i) {
    Mat m;
    if (i < FIRST) {
        u32 a = (u32)(i / PP) + 1;
        u32 r = (u32)(i % PP);
        u32 b = r / P, c = r % P;
        u32 t = mod_p(1 + b * c);
        m.a = a;
        m.b = b;
        m.c = c;
        m.d = mod_p(t * INV[a]);
    } else {
        u64 j = i - FIRST;
        u32 b = (u32)(j / P) + 1, d = (u32)(j % P);
        m.a = 0;
        m.b = b;
        m.c = mod_p(P - INV[b]);  /* c = -b^-1 */
        m.d = d;
    }
    return m;
}

static inline u64 encode_sl(Mat m) {
    if (m.a != 0) return (u64)(m.a - 1) * PP + (u64)m.b * P + m.c;
    return FIRST + (u64)(m.b - 1) * P + m.d;
}

/* Group index of (s,sk) * (g,gk) = (s g, sk + gk). */
static inline u64 lmul(Mat s, u32 sk, Mat g, u32 gk) {
    Mat r;
    r.a = mod_p(s.a * g.a + s.b * g.c);
    r.b = mod_p(s.a * g.b + s.b * g.d);
    r.c = mod_p(s.c * g.a + s.d * g.c);
    r.d = mod_p(s.c * g.b + s.d * g.d);
    u32 k = sk + gk;
    if (k >= NC) k -= NC;
    return encode_sl(r) * NC + k;
}

/* ad - bc == 1 mod p, computed as ad + b(p-c) to stay unsigned. */
static inline int det_is_one(Mat m) {
    u64 s = (u64)m.a * m.d + (u64)m.b * (P - m.c);
    return s % P == 1;
}

/* Startup checks: the SL index is a bijection onto det-1 matrices, fastmod
 * agrees with %, and left-multiplication by s^-1 undoes left-multiplication by s. */
static void verify_encoding(void) {
    u64 x_max = 2ULL * PP;
    if (x_max > (1ULL << 26)) x_max = 1ULL << 26;
    for (u64 x = 0; x <= x_max; x++) {
        if (mod_p((u32)x) != (u32)(x % P)) {
            printf("SELFCHECK FAILED: fastmod at x=%llu\n", (unsigned long long)x);
            exit(2);
        }
    }

    if (P <= 11) {
        /* Brute force: enumerate all of Z_p^4, keep det-1, count and encode. */
        u64 count = 0;
        for (u32 a = 0; a < P; a++)
            for (u32 b = 0; b < P; b++)
                for (u32 c = 0; c < P; c++)
                    for (u32 d = 0; d < P; d++) {
                        Mat m = {a, b, c, d};
                        if (!det_is_one(m)) continue;
                        count++;
                        if (encode_sl(m) >= NSL) {
                            printf("SELFCHECK FAILED: index out of range at (%u,%u,%u,%u)\n", a, b, c, d);
                            exit(2);
                        }
                    }
        if (count != NSL) {
            printf("SELFCHECK FAILED: brute count %llu != p(p^2-1) %llu\n",
                   (unsigned long long)count, (unsigned long long)NSL);
            exit(2);
        }
    }

    /* Round trip over every index: decode lands in det-1 matrices, encode inverts it. */
    for (u64 i = 0; i < NSL; i++) {
        Mat m = decode_sl(i);
        if (!det_is_one(m) || encode_sl(m) != i) {
            printf("SELFCHECK FAILED: SL index round trip at %llu\n", (unsigned long long)i);
            exit(2);
        }
    }

    /* Identity times g is g, on pseudo-random elements. */
    u64 seed = 88172645463325252ULL;
    for (int t = 0; t < 2000; t++) {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        u64 gidx = seed % NG;
        Mat g = decode_sl(gidx / NC);
        u32 gk = (u32)(gidx % NC);
        if (lmul((Mat){1, 0, 0, 1}, 0, g, gk) != gidx) {
            printf("SELFCHECK FAILED: identity times g != g\n");
            exit(2);
        }
    }
}

/* Each generator's inverse undoes it on pseudo-random elements. */
static void verify_generators(const Gen *gen, u32 d) {
    u64 seed = 1442695040888963407ULL;
    for (u32 i = 0; i < d; i++)
        for (int t = 0; t < 500; t++) {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            u64 gidx = seed % NG;
            Mat g = decode_sl(gidx / NC);
            u32 gk = (u32)(gidx % NC);
            u64 sg = lmul(gen[i].m, gen[i].k, g, gk);
            u64 back = lmul(gen[i].mi, gen[i].ki, decode_sl(sg / NC), (u32)(sg % NC));
            if (back != gidx) {
                printf("SELFCHECK FAILED: generator %u inverse does not undo it\n", i + 1);
                exit(2);
            }
        }
}

static u64 bfs(const Gen *gen, u32 d, int side0, u64 *vis[2], u64 *cur, u64 *nxt, u64 W, long *ecc) {
    static const char tag[2] = {'A', 'B'};
    u64 total = 1, level = 0;
    int side = side0;

    memset(vis[0], 0, W * sizeof(u64));
    memset(vis[1], 0, W * sizeof(u64));
    memset(cur, 0, W * sizeof(u64));
    vis[side][0] |= 1ULL;   /* identity (e, side) has index 0 */
    cur[0] |= 1ULL;
    *ecc = 0;

    while (1) {
        int other = 1 - side;
        u64 *vo = vis[other];
        memset(nxt, 0, W * sizeof(u64));

        for (u64 w = 0; w < W; w++) {
            u64 x = cur[w];
            while (x) {
                u64 gidx = (w << 6) + (u64)__builtin_ctzll(x);
                x &= x - 1;
                Mat g = decode_sl(gidx / NC);
                u32 gk = (u32)(gidx % NC);
                for (u32 i = 0; i < d; i++) {
                    u64 t = (side == 0) ? lmul(gen[i].m, gen[i].k, g, gk)
                                        : lmul(gen[i].mi, gen[i].ki, g, gk);
                    if (!((vo[t >> 6] >> (t & 63)) & 1)) nxt[t >> 6] |= 1ULL << (t & 63);
                }
            }
        }

        u64 cnt = 0;
        for (u64 w = 0; w < W; w++) cnt += (u64)__builtin_popcountll(nxt[w]);
        if (cnt == 0) break;

        level++;
        for (u64 w = 0; w < W; w++) vo[w] |= nxt[w];
        total += cnt;
        *ecc = (long)level;
        printf("  from (e,%c) level %llu: new=%llu  reached=%llu / %llu\n", tag[side0],
               (unsigned long long)level, (unsigned long long)cnt, (unsigned long long)total,
               (unsigned long long)(2 * NG));

        u64 *tmp = cur;
        cur = nxt;
        nxt = tmp;
        side = other;
    }
    return total;
}

static int invalid(u32 d, u32 D, const char *reason) {
    printf("INVALID d=%u D=%u vertices=%llu eccA=na eccB=na reason=%s\n", d, D,
           (unsigned long long)(2 * NG), reason);
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s <solution-file>\n", argv[0]);
        return 2;
    }
    FILE *f = fopen(argv[1], "r");
    if (!f) {
        perror(argv[1]);
        return 2;
    }

    char line[512], typ[32], lab1[32], lab2[32];
    u32 d = 0, D = 0, p = 0, nc = 0;
    unsigned long long ntot = 0;
    if (!fgets(line, sizeof line, f) ||
        sscanf(line, "%u %u %31s %u %31s %u %31s %llu", &d, &D, typ, &p, lab1, &nc, lab2, &ntot) != 8) {
        printf("INVALID d=0 D=0 vertices=0 eccA=na eccB=na reason=unparseable header\n");
        return 1;
    }
    if (strcmp(typ, "sl") != 0 || strcmp(lab1, "n") != 0 || strcmp(lab2, "N") != 0) {
        return invalid(d, D, "header is not of the form 'd D sl p n NCYC N NTOT'");
    }
    if (d < 1) return invalid(d, D, "d < 1");
    if (p < 2 || p >= 40000) return invalid(d, D, "p out of supported range 2..39999");
    for (u32 q = 2; (u64)q * q <= p; q++)
        if (p % q == 0) return invalid(d, D, "p is not prime");
    if (nc < 1) return invalid(d, D, "n < 1");

    setup(p, nc);
    if (ntot != NG) {
        printf("INVALID d=%u D=%u vertices=%llu eccA=na eccB=na reason=NTOT %llu != p(p^2-1)*n = %llu\n",
               d, D, (unsigned long long)(2 * NG), ntot, (unsigned long long)NG);
        return 1;
    }

    printf("file=%s d=%u D=%u p=%u n=%u |G|=%llu vertices=%llu\n", argv[1], d, D, p, nc,
           (unsigned long long)NG, (unsigned long long)(2 * NG));

    double t0 = now_sec();
    verify_encoding();
    printf("selfcheck: SL(2,%u) index is a bijection onto det-1 matrices (|SL|=%llu), fastmod ok (%.2fs)\n",
           p, (unsigned long long)NSL, now_sec() - t0);

    /* Read the d generators. */
    Gen *gen = calloc(d, sizeof(Gen));
    for (u32 i = 0; i < d; i++) {
        long a, b, c, dd, k;
        if (fscanf(f, " %*s mat(%ld,%ld,%ld,%ld) z=%ld", &a, &b, &c, &dd, &k) != 5) {
            char r[128];
            snprintf(r, sizeof r, "generator line %u is unparseable", i + 1);
            return invalid(d, D, r);
        }
        char r[128];
        if (a < 0 || b < 0 || c < 0 || dd < 0 || a >= p || b >= p || c >= p || dd >= p) {
            snprintf(r, sizeof r, "generator %u has a matrix entry outside 0..p-1", i + 1);
            return invalid(d, D, r);
        }
        if (k < 0 || k >= nc) {
            snprintf(r, sizeof r, "generator %u has z outside 0..n-1", i + 1);
            return invalid(d, D, r);
        }
        long det = ((a * dd - b * c) % (long)p + (long)p) % (long)p;
        if (det != 1) {
            snprintf(r, sizeof r, "generator %u is not in SL(2,p): det = %ld", i + 1, det);
            return invalid(d, D, r);
        }
        gen[i].m = (Mat){(u32)a, (u32)b, (u32)c, (u32)dd};
        gen[i].k = (u32)k;
        gen[i].mi = (Mat){(u32)dd, (u32)((p - b) % p), (u32)((p - c) % p), (u32)a};
        gen[i].ki = (nc - (u32)k) % nc;
    }
    {
        int ch;
        while ((ch = fgetc(f)) != EOF && isspace(ch)) {
        }
        if (ch != EOF) return invalid(d, D, "more generator lines than d");
    }
    fclose(f);

    for (u32 i = 0; i < d; i++)
        for (u32 j = 0; j < i; j++) {
            Mat x = gen[i].m, y = gen[j].m;
            if (x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d && gen[i].k == gen[j].k) {
                char r[128];
                snprintf(r, sizeof r, "generator %u duplicates generator %u", i + 1, j + 1);
                return invalid(d, D, r);
            }
        }
    printf("generators: %u read, all in SL(2,%u) x Z_%u, all distinct\n", d, p, nc);
    verify_generators(gen, d);
    printf("selfcheck: generator inverses verified\n");

    /* Bitsets over G. */
    u64 W = (NG + 63) / 64;
    u64 *visA = calloc(W, sizeof(u64));
    u64 *visB = calloc(W, sizeof(u64));
    u64 *cur = calloc(W, sizeof(u64));
    u64 *nxt = calloc(W, sizeof(u64));
    if (!visA || !visB || !cur || !nxt) {
        printf("INVALID d=%u D=%u vertices=%llu eccA=na eccB=na reason=out of memory\n", d, D,
               (unsigned long long)(2 * NG));
        return 1;
    }
    u64 *vis[2] = {visA, visB};

    long eA = -1, eB = -1;
    u64 rA = 0, rB = 0;

    t0 = now_sec();
    printf("BFS from (e,A):\n");
    rA = bfs(gen, d, 0, vis, cur, nxt, W, &eA);
    printf("  done in %.2fs, eccA=%ld, reached %llu / %llu\n", now_sec() - t0, eA,
           (unsigned long long)rA, (unsigned long long)(2 * NG));

    t0 = now_sec();
    printf("BFS from (e,B):\n");
    rB = bfs(gen, d, 1, vis, cur, nxt, W, &eB);
    printf("  done in %.2fs, eccB=%ld, reached %llu / %llu\n", now_sec() - t0, eB,
           (unsigned long long)rB, (unsigned long long)(2 * NG));

    char sA[24], sB[24], reason[256];
    int connected = (rA == 2 * NG) && (rB == 2 * NG);
    if (rA == 2 * NG) snprintf(sA, sizeof sA, "%ld", eA); else snprintf(sA, sizeof sA, "inf");
    if (rB == 2 * NG) snprintf(sB, sizeof sB, "%ld", eB); else snprintf(sB, sizeof sB, "inf");

    if (connected && eA <= (long)D && eB <= (long)D) {
        printf("VALID d=%u D=%u vertices=%llu eccA=%s eccB=%s\n", d, D, (unsigned long long)(2 * NG), sA, sB);
        return 0;
    }
    if (!connected) {
        snprintf(reason, sizeof reason, "not connected (from (e,A) reached %llu, from (e,B) reached %llu, of %llu)",
                 (unsigned long long)rA, (unsigned long long)rB, (unsigned long long)(2 * NG));
    } else if (eA > (long)D) {
        snprintf(reason, sizeof reason, "eccA %ld > D %u", eA, D);
    } else {
        snprintf(reason, sizeof reason, "eccB %ld > D %u", eB, D);
    }
    printf("INVALID d=%u D=%u vertices=%llu eccA=%s eccB=%s reason=%s\n", d, D, (unsigned long long)(2 * NG), sA, sB,
           reason);
    return 1;
}
