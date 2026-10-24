/* haarcheck_pgl: low-memory exact check of a Haar graph H(G,S), G = PGL(2,p) x Z_n, p an odd prime (card B3).
 *
 * Usage: haarcheck_pgl SOLUTION.txt        exit 0 iff VALID, 1 iff INVALID (also malformed input), 2 usage error.
 *
 * Solution file (as written by research/structured/haar_sym.c for the "pgl p" family):
 *   header   "d D pgl p n NCYC N NTOT"          (N NTOT optional; must equal p(p^2-1)*NCYC if present)
 *   d lines  "<index> mat(a,b,c,d) z=Z"         (the first token is ignored, as in research/frontier/build_haar2.py)
 *
 * Element encoding (same canonical form as build_haar2.py canon_key and haar_sym mkey): a 2x2 invertible matrix over
 * GF(p) modulo scalars is stored with its first nonzero entry of (a,b) equal to 1.  Canonical matrices are ranked in O(1):
 *   a != 0 (so a = 1):  (1,b,c,d) with d != bc,  rank = (b*p + c)*(p-1) + (d < bc ? d : d-1)
 *   a == 0 (so b = 1):  (0,1,c,d) with c != 0,  rank = p*p*(p-1) + (c-1)*p + d
 * Hence |PGL(2,p)| = p(p^2-1), the identity (1,0,0,1) has rank 0, and the group element (M,z) has index rank(M)*n + z.
 * Left multiplication by the generator s = (M_s, z_s) is (M_s M, z_s + z) (direct product with Z_n, no twist).
 *
 * Haar graph: vertices (g,A) = g and (g,B) = N + g with N = p(p^2-1) n; edges (g,A) ~ (s g, B) for the d generators s.
 * Right multiplication by G is transitive on each side, so diam = max(ecc(e,A), ecc(e,B)) and two BFS (from (e,A), from
 * (e,B)) decide validity: VALID iff all 2N vertices are reached from both sources within D steps.  The generators must be
 * d distinct elements (otherwise INVALID, as build_haar2.py rejects them).
 * Memory: three bitsets of 2N bits (visited, frontier, next); no adjacency lists.
 *
 * Output: information lines (group, eccentricities, time), then the last line
 *   "VALID d=.. D=.. vertices=.. eccA=.. eccB=.."   or   "INVALID d=.. D=.. vertices=.. eccA=.. eccB=.. unreached=.."
 * (or "INVALID reason=..." for a malformed or non-group input).
 */
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <ctype.h>

typedef uint64_t u64;

#define MAXD 64

static u64 P, NCYC, NPGL, N, NV, NW;
static long long DLIM;
static int ND;
static u64 *INV;                                  /* INV[x] = x^-1 mod p, x = 1..p-1 */
static u64 SA[MAXD], SB[MAXD], SC[MAXD], SD[MAXD], SZ[MAXD];   /* generator matrices and z */
static u64 IA[MAXD], IB[MAXD], IC[MAXD], ID[MAXD], NZ[MAXD];   /* adjugates (= inverses up to scalars), -z mod n */
static u64 *VIS, *CUR, *NXT;

static void invalid(const char *why) {
    printf("INVALID reason=%s\n", why);
    exit(1);
}

static u64 powmod(u64 b, u64 e, u64 m) {
    u64 r = 1 % m; b %= m;
    while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static int is_prime(u64 x) {
    if (x < 2) return 0;
    for (u64 t = 2; t * t <= x; t++) if (x % t == 0) return 0;
    return 1;
}

/* rank of a canonical matrix; (a,b,c,d) in [0,p)^4 with ad - bc != 0 (any scalar multiple is fine) */
static u64 enc(u64 a, u64 b, u64 c, u64 d) {
    if (a) {
        u64 ia = INV[a];
        b = b * ia % P; c = c * ia % P; d = d * ia % P;      /* now a = 1 */
        u64 m = b * c % P;                                  /* d != m since det = d - bc != 0 */
        u64 r = d < m ? d : d - 1;
        return (b * P + c) * (P - 1) + r;
    } else {
        u64 ib = INV[b];                                    /* a = 0: b, c != 0 */
        c = c * ib % P; d = d * ib % P;                     /* now b = 1 */
        return P * P * (P - 1) + (c - 1) * P + d;
    }
}

static void dec(u64 idx, u64 *a, u64 *b, u64 *c, u64 *d) {
    u64 base = P * P * (P - 1);
    if (idx < base) {
        u64 r = idx % (P - 1), bc = idx / (P - 1);
        u64 cc = bc % P, bb = bc / P;
        u64 m = bb * cc % P;
        *a = 1; *b = bb; *c = cc; *d = r < m ? r : r + 1;
    } else {
        u64 j = idx - base;
        *a = 0; *b = 1; *c = j / P + 1; *d = j % P;
    }
}

static inline int getbit(const u64 *B, u64 v) { return (int)((B[v >> 6] >> (v & 63)) & 1); }
static inline void setbit(u64 *B, u64 v) { B[v >> 6] |= 1ULL << (v & 63); }

/* BFS from src (vertex id: A-side g < N, B-side N + g) over the bipartite Haar graph.  Sets ecc = last nonempty level and
 * count = number of reached vertices. */
static void bfs(u64 src, u64 *ecc, u64 *count) {
    memset(VIS, 0, NW * 8);
    memset(CUR, 0, NW * 8);
    setbit(VIS, src); setbit(CUR, src);
    u64 cnt = 1, level = 0;
    for (;;) {
        memset(NXT, 0, NW * 8);
        u64 added = 0;
        for (u64 w = 0; w < NW; w++) {
            u64 x = CUR[w];
            while (x) {
                u64 v = (w << 6) + (u64)__builtin_ctzll(x);
                x &= x - 1;
                u64 a, b, c, d;
                if (v < N) {                                /* (g,A) -> (s g, B) */
                    u64 qi = v / NCYC, z = v - qi * NCYC;
                    dec(qi, &a, &b, &c, &d);
                    for (int t = 0; t < ND; t++) {
                        u64 na = (SA[t] * a + SB[t] * c) % P, nb = (SA[t] * b + SB[t] * d) % P;
                        u64 nc = (SC[t] * a + SD[t] * c) % P, nd = (SC[t] * b + SD[t] * d) % P;
                        u64 z2 = z + SZ[t]; if (z2 >= NCYC) z2 -= NCYC;
                        u64 u = N + enc(na, nb, nc, nd) * NCYC + z2;
                        if (!getbit(VIS, u)) { setbit(VIS, u); setbit(NXT, u); added++; }
                    }
                } else {                                    /* (h,B) -> (s^-1 h, A) */
                    u64 h = v - N;
                    u64 qi = h / NCYC, z = h - qi * NCYC;
                    dec(qi, &a, &b, &c, &d);
                    for (int t = 0; t < ND; t++) {
                        u64 na = (IA[t] * a + IB[t] * c) % P, nb = (IA[t] * b + IB[t] * d) % P;
                        u64 nc = (IC[t] * a + ID[t] * c) % P, nd = (IC[t] * b + ID[t] * d) % P;
                        u64 z2 = z + NZ[t]; if (z2 >= NCYC) z2 -= NCYC;
                        u64 u = enc(na, nb, nc, nd) * NCYC + z2;
                        if (!getbit(VIS, u)) { setbit(VIS, u); setbit(NXT, u); added++; }
                    }
                }
            }
        }
        if (!added) break;
        cnt += added; level++;
        u64 *T = CUR; CUR = NXT; NXT = T;
    }
    *ecc = level; *count = cnt;
}

static double now_s(void) {
    struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static int tokenize(char *s, char **tok, int max) {
    int n = 0;
    for (char *t = strtok(s, " \t\r\n"); t && n < max; t = strtok(NULL, " \t\r\n")) tok[n++] = t;
    return n;
}

static int blank(const char *s) {
    for (; *s; s++) if (!isspace((unsigned char)*s)) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: haarcheck_pgl SOLUTION.txt\n"); return 2; }
    double t0 = now_s();
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror(argv[1]); return 2; }
    static char line[8192];
    static char *tok[80];
    int nt = 0;

    do { if (!fgets(line, sizeof line, f)) invalid("empty file"); } while (blank(line));
    nt = tokenize(line, tok, 80);
    if (nt < 5) invalid("short header");
    long long d = atoll(tok[0]);
    DLIM = atoll(tok[1]);
    if (d < 1 || d > MAXD) invalid("bad d");
    if (DLIM < 0) invalid("bad D");
    if (strcmp(tok[2], "pgl") != 0) invalid("family is not pgl (only 'pgl p' is supported here)");
    char *end = NULL;
    P = strtoull(tok[3], &end, 10);
    if (*end || P < 2 || P > 1000000) invalid("bad p");
    if (!is_prime(P)) invalid("p is not prime");
    int ni = -1;
    for (int i = 4; i < nt; i++) if (!strcmp(tok[i], "n")) { ni = i; break; }
    if (ni != 4) invalid("header group must be exactly 'pgl p' (no poly or other tokens)");
    if (ni + 1 >= nt) invalid("header has no n value");
    NCYC = strtoull(tok[ni + 1], &end, 10);
    if (*end || NCYC < 1) invalid("bad n");
    NPGL = P * (P * P - 1);
    if (NPGL > (1ULL << 40) / NCYC / 2) invalid("group too large for this checker");
    N = NPGL * NCYC;
    NV = 2 * N;
    for (int i = ni + 2; i + 1 < nt; i++)
        if (!strcmp(tok[i], "N") && strtoull(tok[i + 1], NULL, 10) != N) invalid("declared N does not match p(p^2-1)*n");
    ND = (int)d;

    INV = malloc(sizeof(u64) * P);
    if (!INV) { fprintf(stderr, "out of memory\n"); return 2; }
    INV[0] = 0;
    for (u64 x = 1; x < P; x++) INV[x] = powmod(x, P - 2, P);

    u64 qis[MAXD], zs[MAXD];
    for (int i = 0; i < ND; i++) {
        do { if (!fgets(line, sizeof line, f)) invalid("missing generator lines"); } while (blank(line));
        char *p = line;
        while (*p == ' ' || *p == '\t') p++;
        while (*p && !isspace((unsigned char)*p)) p++;          /* the index token is ignored */
        while (*p == ' ' || *p == '\t') p++;
        unsigned long long a, b, c, dd, z; int used = 0;
        if (sscanf(p, "mat(%llu,%llu,%llu,%llu) z=%llu%n", &a, &b, &c, &dd, &z, &used) != 5) invalid("bad generator line");
        char *r = p + used;
        while (*r && isspace((unsigned char)*r)) r++;
        if (*r) invalid("trailing text in generator line");
        if (a >= P || b >= P || c >= P || dd >= P) invalid("matrix entry out of range");
        if (z >= NCYC) invalid("generator z out of range");
        if (((a * dd) % P + P - (b * c) % P) % P == 0) invalid("generator matrix is not invertible");
        SA[i] = a; SB[i] = b; SC[i] = c; SD[i] = dd; SZ[i] = z;
        IA[i] = dd; IB[i] = (P - b) % P; IC[i] = (P - c) % P; ID[i] = a; NZ[i] = (NCYC - z) % NCYC;
        qis[i] = enc(a, b, c, dd); zs[i] = z;
        for (int j = 0; j < i; j++) if (qis[j] == qis[i] && zs[j] == zs[i]) invalid("repeated generator");
    }
    fclose(f);

    NW = (NV + 63) / 64;
    VIS = calloc(NW, 8); CUR = calloc(NW, 8); NXT = calloc(NW, 8);
    if (!VIS || !CUR || !NXT) { fprintf(stderr, "out of memory\n"); return 2; }
    printf("group=pgl %llu x Z_%llu N=%llu vertices=%llu d=%d D=%lld (parsed in %.2fs)\n",
           (unsigned long long)P, (unsigned long long)NCYC, (unsigned long long)N, (unsigned long long)NV, ND, DLIM,
           now_s() - t0);

    u64 eA = 0, eB = 0, cA = 0, cB = 0;
    double t1 = now_s();
    bfs(0, &eA, &cA);                                       /* (e,A): identity has rank 0, z = 0 */
    printf("ecc from A = %llu unreached %llu (%.2fs)\n", (unsigned long long)eA, (unsigned long long)(NV - cA), now_s() - t1);
    t1 = now_s();
    bfs(N, &eB, &cB);                                       /* (e,B) */
    printf("ecc from B = %llu unreached %llu (%.2fs)\n", (unsigned long long)eB, (unsigned long long)(NV - cB), now_s() - t1);

    u64 uA = NV - cA, uB = NV - cB;
    int ok = uA == 0 && uB == 0 && eA <= (u64)DLIM && eB <= (u64)DLIM;
    if (ok)
        printf("VALID d=%d D=%lld vertices=%llu eccA=%llu eccB=%llu\n", ND, DLIM, (unsigned long long)NV,
               (unsigned long long)eA, (unsigned long long)eB);
    else
        printf("INVALID d=%d D=%lld vertices=%llu eccA=%llu eccB=%llu unreached=%llu,%llu\n", ND, DLIM,
               (unsigned long long)NV, (unsigned long long)eA, (unsigned long long)eB, (unsigned long long)uA,
               (unsigned long long)uB);
    free(VIS); free(CUR); free(NXT); free(INV);
    return ok ? 0 : 1;
}
