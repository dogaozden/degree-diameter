/* lift.c: annealing search for regular voltage lifts of a bipartite base multigraph, diameter <= D.

   Lift of base B (vertices 0..k-1, edges e = {x,y}, x white, y black, voltage a_e in a group G of order N):
       vertices (u,g), u in V(B), g in G;  edges (x,g) ~ (y, a_e g)  for every base edge e and g in G.
   Right multiplication (u,g) -> (u,gh) is an automorphism, so ecc(u,g) = ecc(u,1) and
       diam(lift) = max_u ecc((u,1)):  k BFS's, one per base vertex.
   The search cost is the number of pairs (source (u,1), lift vertex w) with dist > D, summed over u.
   BFS: a 64-bit mask per lift vertex (bit = source), sources of one colour per pass, in-place by parity.

   Usage:
     lift search BASE D SECONDS SEED K OUT GROUP...    anneal the free voltages; write OUT if cost 0
     lift check SOL [EDGES]                            exact BFS (int distances) from every (u,1); optional edge list
     lift sample BASE D M GROUP...                     cost quantiles of M random voltage assignments (screening)
   GROUP := FACTOR [x FACTOR]...,  FACTOR := cyc n | meta m k r | dih n | sl p | psl p | pgl p   (p prime)
     meta m k r = Z_m x|_r Z_k, (a,j)(b,l) = (a + r^j b, j + l), needs r^k = 1 mod m.  dih n = meta n 2 n-1.
   Element text: components joined by '|'; cyc "a", meta "a,j", sl/psl/pgl "a,b,c,d" = [[a,b],[c,d]].
   BASE file: "k K" then lines "e x y" (free voltage) or "e x y = ELEM" (fixed); '#' comments.
     Edges of a BFS spanning tree that are free get the identity (gauge fixing) unless NOGAUGE=1.
   Env: TMAX TMIN COOL REHEAT TARGP UCAP (as in haar_gen3), REPORT seconds between progress lines.
*/
#include <math.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

/* ------------------------------------------------------------------ rng, time */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timeval tv; gettimeofday(&tv, NULL); return tv.tv_sec + 1e-6 * tv.tv_usec; }
static void die(const char *m) { fprintf(stderr, "error: %s\n", m); exit(2); }

/* ------------------------------------------------------------------ groups */
enum { F_CYC, F_META, F_SL, F_PSL, F_PGL };
typedef struct {
    int type, n;            /* order */
    int m, k, r;            /* cyc: m = n; meta: m, k, r */
    int p;                  /* matrix groups */
    int *rpow;              /* meta: r^j mod m */
    uint16_t *E;            /* matrix entries, 4 per element */
    uint64_t *hkey; int *hval; size_t hcap;   /* matrix index hash */
    int *inv;               /* inverse table */
    char spec[64];
} factor;

#define MAXF 8
static factor FS[MAXF];
static int nf = 0, N = 1, IDENT = 0;
static int RAD[MAXF];       /* mixed radix: index = sum c_i * RAD[i] */
static char GSPEC[512];

static size_t hslot(const factor *f, uint64_t key) {
    size_t h = (size_t)((key * 0x9E3779B97F4A7C15ULL) >> 20) & (f->hcap - 1);
    while (f->hkey[h] != UINT64_MAX && f->hkey[h] != key) h = (h + 1) & (f->hcap - 1);
    return h;
}
static void mnorm(const factor *f, int *a) {   /* canonical representative of a matrix */
    int p = f->p;
    if (f->type == F_PSL) {   /* smaller of +-A, lexicographic */
        int b[4]; for (int i = 0; i < 4; i++) b[i] = (p - a[i]) % p;
        for (int i = 0; i < 4; i++) { if (b[i] < a[i]) { memcpy(a, b, sizeof b); return; } if (b[i] > a[i]) return; }
    } else if (f->type == F_PGL) {   /* first nonzero entry 1 */
        int i = 0; while (a[i] == 0) i++;
        long long s = 1, b = a[i], e = p - 2; while (e) { if (e & 1) s = s * b % p; b = b * b % p; e >>= 1; }
        for (int j = 0; j < 4; j++) a[j] = (int)(a[j] * s % p);
    }
}
static int mindex(const factor *f, const int *a) {
    uint64_t key = (((uint64_t)a[0] * f->p + a[1]) * f->p + a[2]) * f->p + a[3];
    size_t h = hslot(f, key); return f->hkey[h] == key ? f->hval[h] : -1;
}
static int fmul(const factor *f, int x, int y) {
    switch (f->type) {
    case F_CYC: return (x + y) % f->n;
    case F_META: {
        int a = x / f->k, j = x % f->k, b = y / f->k, l = y % f->k;
        return (int)((a + (long long)f->rpow[j] * b) % f->m) * f->k + (j + l) % f->k;
    }
    default: {
        const uint16_t *A = f->E + 4 * (size_t)x, *B = f->E + 4 * (size_t)y; int p = f->p, c[4];
        c[0] = (A[0] * B[0] + A[1] * B[2]) % p; c[1] = (A[0] * B[1] + A[1] * B[3]) % p;
        c[2] = (A[2] * B[0] + A[3] * B[2]) % p; c[3] = (A[2] * B[1] + A[3] * B[3]) % p;
        mnorm(f, c); return mindex(f, c);
    }
    }
}
static int isprime(int p) { if (p < 2) return 0; for (int d = 2; d * d <= p; d++) if (p % d == 0) return 0; return 1; }
static void build_factor(factor *f) {
    if (f->type == F_CYC) { f->n = f->m; snprintf(f->spec, 64, "cyc %d", f->m); }
    else if (f->type == F_META) {
        f->n = f->m * f->k; f->rpow = malloc(sizeof(int) * f->k); f->rpow[0] = 1 % f->m;
        for (int j = 1; j < f->k; j++) f->rpow[j] = (int)((long long)f->rpow[j - 1] * f->r % f->m);
        if ((long long)f->rpow[f->k - 1] * f->r % f->m != 1 % f->m) die("meta: r^k != 1 mod m");
        snprintf(f->spec, 64, "meta %d %d %d", f->m, f->k, f->r);
    } else {
        int p = f->p; if (!isprime(p) || p > 250) die("matrix groups need p prime <= 250");
        long long cnt = 0; int a[4];
        f->E = NULL;
        for (int pass = 0; pass < 2; pass++) {
            if (pass == 1) {
                f->E = malloc(sizeof(uint16_t) * 4 * (size_t)cnt);
                f->hcap = 1; while (f->hcap < (size_t)cnt * 2 + 16) f->hcap <<= 1;
                f->hkey = malloc(sizeof(uint64_t) * f->hcap); f->hval = malloc(sizeof(int) * f->hcap);
                for (size_t i = 0; i < f->hcap; i++) f->hkey[i] = UINT64_MAX;
                cnt = 0;
            }
            /* candidates: SL/PSL solve for the last free entry; PGL first nonzero entry = 1 */
            for (int x0 = 0; x0 < p; x0++) for (int x1 = 0; x1 < p; x1++) for (int x2 = 0; x2 < p; x2++) for (int x3 = 0; x3 < p; x3++) {
                if (f->type == F_PGL) {
                    if (x0 > 1) goto next;
                    if (x0 == 0 && x1 != 1) goto next;
                    a[0] = x0; a[1] = x1; a[2] = x2; a[3] = x3;
                } else {
                    a[0] = x0; a[1] = x1; a[2] = x2;
                    if (x0) {   /* d = (1 + b c) / a, generated once (x3 == 0) */
                        if (x3) goto next;
                        long long s = 1, bb = x0, ee = p - 2; while (ee) { if (ee & 1) s = s * bb % p; bb = bb * bb % p; ee >>= 1; }
                        a[3] = (int)((1 + (long long)x1 * x2) % p * s % p);
                    } else a[3] = x3;
                }
                {
                    int det = (int)(((long long)a[0] * a[3] - (long long)a[1] * a[2]) % p); if (det < 0) det += p;
                    if (f->type == F_PGL ? det == 0 : det != 1) goto next;
                    int b[4]; memcpy(b, a, sizeof b); mnorm(f, b); if (memcmp(a, b, sizeof b)) goto next;
                    if (pass == 1) {
                        for (int i = 0; i < 4; i++) f->E[4 * cnt + i] = (uint16_t)a[i];
                        uint64_t key = (((uint64_t)a[0] * p + a[1]) * p + a[2]) * p + a[3];
                        size_t h = hslot(f, key); f->hkey[h] = key; f->hval[h] = (int)cnt;
                    }
                    cnt++;
                }
                next:;
            }
        }
        if (cnt > 2000000000LL) die("group too large");
        f->n = (int)cnt;
        snprintf(f->spec, 64, "%s %d", f->type == F_SL ? "sl" : f->type == F_PSL ? "psl" : "pgl", p);
    }
    /* identity of this factor */
    int id = 0;
    if (f->type >= F_SL) { int c[4] = {1, 0, 0, 1}; mnorm(f, c); id = mindex(f, c); }
    /* inverse table by search over orders would be slow; use formulas */
    f->inv = malloc(sizeof(int) * f->n);
    for (int x = 0; x < f->n; x++) {
        if (f->type == F_CYC) f->inv[x] = (f->n - x) % f->n;
        else if (f->type == F_META) {   /* (a,j)^-1 = (-r^{-j} a, -j) */
            int a = x / f->k, j = x % f->k, jj = (f->k - j) % f->k;
            int y = (int)((f->m - (long long)f->rpow[jj] * a % f->m) % f->m);
            f->inv[x] = y * f->k + jj;
        } else {
            const uint16_t *A = f->E + 4 * (size_t)x; int p = f->p, c[4];
            c[0] = A[3]; c[1] = (p - A[1]) % p; c[2] = (p - A[2]) % p; c[3] = A[0];   /* adj = det * inverse */
            mnorm(f, c); f->inv[x] = mindex(f, c);
        }
    }
    (void)id;
}
static int factor_ident(const factor *f) {
    if (f->type < F_SL) return 0;
    int c[4] = {1, 0, 0, 1}; mnorm(f, c); return mindex(f, c);
}
static int gmul(int x, int y) {
    int z = 0;
    for (int i = 0; i < nf; i++) { int xi = (x / RAD[i]) % FS[i].n, yi = (y / RAD[i]) % FS[i].n; z += fmul(&FS[i], xi, yi) * RAD[i]; }
    return z;
}
static int ginv(int x) {
    int z = 0;
    for (int i = 0; i < nf; i++) { int xi = (x / RAD[i]) % FS[i].n; z += FS[i].inv[xi] * RAD[i]; }
    return z;
}
static void gdesc(int x, char *buf) {
    buf[0] = 0;
    for (int i = 0; i < nf; i++) {
        const factor *f = &FS[i]; int xi = (x / RAD[i]) % f->n; char t[64];
        if (f->type == F_CYC) sprintf(t, "%d", xi);
        else if (f->type == F_META) sprintf(t, "%d,%d", xi / f->k, xi % f->k);
        else { const uint16_t *A = f->E + 4 * (size_t)xi; sprintf(t, "%d,%d,%d,%d", A[0], A[1], A[2], A[3]); }
        if (i) strcat(buf, "|");
        strcat(buf, t);
    }
}
static int gparse(const char *s) {   /* returns -1 on error */
    int z = 0; const char *p = s;
    for (int i = 0; i < nf; i++) {
        const factor *f = &FS[i]; int v[4], c = 0;
        while (c < 4) {
            char *end; long t = strtol(p, &end, 10); if (end == p) return -1;
            v[c++] = (int)t; p = end;
            if (*p == ',') { p++; continue; }
            break;
        }
        int xi;
        if (f->type == F_CYC) { if (c != 1) return -1; xi = ((v[0] % f->n) + f->n) % f->n; }
        else if (f->type == F_META) { if (c != 2) return -1; xi = (((v[0] % f->m) + f->m) % f->m) * f->k + ((v[1] % f->k) + f->k) % f->k; }
        else {
            if (c != 4) return -1;
            int a[4]; for (int j = 0; j < 4; j++) a[j] = ((v[j] % f->p) + f->p) % f->p;
            int det = (int)(((long long)a[0] * a[3] - (long long)a[1] * a[2]) % f->p); if (det < 0) det += f->p;
            if (f->type == F_PGL ? det == 0 : det != 1) return -1;
            mnorm(f, a); xi = mindex(f, a); if (xi < 0) return -1;
        }
        z += xi * RAD[i];
        if (i + 1 < nf) { if (*p != '|') return -1; p++; }
    }
    while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r') p++;
    return *p ? -1 : z;
}
/* keep the fixed factors of edge e's voltage, take the free ones from x */
static int restrict_volt(int e, int x);
/* parse GROUP tokens argv[*a..]; stops at end */
static void parse_group(int argc, char **argv, int *a) {
    GSPEC[0] = 0;
    while (*a < argc) {
        if (nf == MAXF) die("too many factors");
        factor *f = &FS[nf]; memset(f, 0, sizeof *f);
        const char *t = argv[*a];
        if (!strcmp(t, "cyc")) { f->type = F_CYC; f->m = atoi(argv[*a + 1]); *a += 2; }
        else if (!strcmp(t, "meta")) { f->type = F_META; f->m = atoi(argv[*a + 1]); f->k = atoi(argv[*a + 2]); f->r = atoi(argv[*a + 3]); *a += 4; }
        else if (!strcmp(t, "dih")) { f->type = F_META; f->m = atoi(argv[*a + 1]); f->k = 2; f->r = f->m - 1; *a += 2; }
        else if (!strcmp(t, "sl")) { f->type = F_SL; f->p = atoi(argv[*a + 1]); *a += 2; }
        else if (!strcmp(t, "psl")) { f->type = F_PSL; f->p = atoi(argv[*a + 1]); *a += 2; }
        else if (!strcmp(t, "pgl")) { f->type = F_PGL; f->p = atoi(argv[*a + 1]); *a += 2; }
        else die("unknown group factor");
        if (*a > argc) die("missing group parameter");
        if ((f->type == F_CYC && f->m < 1) || (f->type == F_META && (f->m < 1 || f->k < 1))) die("bad group parameter");
        build_factor(f); nf++;
        if (GSPEC[0]) strcat(GSPEC, " x ");
        strcat(GSPEC, f->spec);
        if (*a < argc && !strcmp(argv[*a], "x")) { (*a)++; continue; }
        break;
    }
    if (nf == 0) die("no group");
    long long n = 1; for (int i = nf - 1; i >= 0; i--) { RAD[i] = (int)n; n *= FS[i].n; }
    if (n > (1LL << 30)) die("group too large");
    N = (int)n; IDENT = 0; for (int i = 0; i < nf; i++) IDENT += factor_ident(&FS[i]) * RAD[i];
    /* sanity: associativity, identity, inverse on random triples */
    uint64_t save = rs; rs = 0x1234567ULL;
    for (int t = 0; t < 3000; t++) {
        int x = rnd() % N, y = rnd() % N, z = rnd() % N;
        if (gmul(gmul(x, y), z) != gmul(x, gmul(y, z)) || gmul(x, ginv(x)) != IDENT || gmul(IDENT, x) != x || gmul(x, IDENT) != x) die("group axioms fail");
    }
    rs = save;
}

/* ------------------------------------------------------------------ base graph */
#define MAXE 4000000
static int K, E;                 /* base vertices, edges */
static int EX[MAXE], EY[MAXE];   /* x white, y black (after orientation) */
static int VOLT[MAXE], FIXED[MAXE];   /* FIXED: 0 free, 1 fixed, 2 partly fixed (some factors free) */
static int PMASK[MAXE];                /* partly fixed: bit i set = factor i free */
static int *COL;                 /* 0 white, 1 black */
static int *DEG, MAXDEG;
static int *FREE, NFREE;         /* indices of free edges */

static void read_base(const char *fn, int want_volt_text) { (void)want_volt_text;
    FILE *fp = fopen(fn, "r"); if (!fp) { perror(fn); exit(2); }
    char line[4096]; K = -1; E = 0;
    static char *vtxt[MAXE];
    while (fgets(line, sizeof line, fp)) {
        char *h = strchr(line, '#'); if (h) *h = 0;
        char *p = line; while (*p == ' ' || *p == '\t') p++;
        if (!*p || *p == '\n') continue;
        if (p[0] == 'k' && (p[1] == ' ' || p[1] == '\t')) { K = atoi(p + 1); continue; }
        if (p[0] == 'e' && (p[1] == ' ' || p[1] == '\t')) {
            if (E == MAXE) die("too many edges");
            int x, y, n; if (sscanf(p + 1, "%d %d%n", &x, &y, &n) != 2) die("bad edge line");
            EX[E] = x; EY[E] = y; FIXED[E] = 0; vtxt[E] = NULL;
            char *q = strchr(p + 1 + n, '=');
            if (q) { q++; while (*q == ' ') q++; char *e2 = q + strlen(q); while (e2 > q && (e2[-1] == '\n' || e2[-1] == ' ' || e2[-1] == '\r')) *--e2 = 0; vtxt[E] = strdup(q); FIXED[E] = 1; }
            E++; continue;
        }
        /* other lines (header of solution files) ignored */
    }
    fclose(fp);
    if (K <= 0) die("base: missing k");
    COL = malloc(sizeof(int) * K); DEG = calloc(K, sizeof(int));
    for (int v = 0; v < K; v++) COL[v] = -1;
    /* 2-colour */
    int *adjn = calloc(K + 1, sizeof(int)), *adj = malloc(sizeof(int) * 2 * E);
    for (int e = 0; e < E; e++) { if (EX[e] < 0 || EX[e] >= K || EY[e] < 0 || EY[e] >= K) die("edge endpoint out of range"); if (EX[e] == EY[e]) die("loop in base (not bipartite)"); adjn[EX[e] + 1]++; adjn[EY[e] + 1]++; }
    for (int v = 0; v < K; v++) adjn[v + 1] += adjn[v];
    int *fill = calloc(K, sizeof(int));
    for (int e = 0; e < E; e++) { adj[adjn[EX[e]] + fill[EX[e]]++] = e; adj[adjn[EY[e]] + fill[EY[e]]++] = e; }
    int *qu = malloc(sizeof(int) * K), comps = 0;
    for (int s = 0; s < K; s++) if (COL[s] < 0) {
        comps++; int h = 0, t = 0; qu[t++] = s; COL[s] = 0;
        while (h < t) { int v = qu[h++]; for (int i = adjn[v]; i < adjn[v + 1]; i++) { int e = adj[i], w = EX[e] == v ? EY[e] : EX[e];
            if (COL[w] < 0) { COL[w] = COL[v] ^ 1; qu[t++] = w; } else if (COL[w] == COL[v]) die("base graph is not bipartite"); } }
    }
    if (comps != 1) die("base graph is not connected");
    for (int e = 0; e < E; e++) { if (COL[EX[e]] == 1) { int t = EX[e]; EX[e] = EY[e]; EY[e] = t; } DEG[EX[e]]++; DEG[EY[e]]++; }
    MAXDEG = 0; for (int v = 0; v < K; v++) if (DEG[v] > MAXDEG) MAXDEG = DEG[v];
    /* voltages: parse fixed; a fixed voltage given for an edge stored y->x in the file is inverted */
    for (int e = 0; e < E; e++) VOLT[e] = IDENT;
    {
        /* recompute original orientation by re-reading the file */
        FILE *fq = fopen(fn, "r"); int e = 0;
        while (fgets(line, sizeof line, fq)) {
            char *h = strchr(line, '#'); if (h) *h = 0;
            char *p = line; while (*p == ' ' || *p == '\t') p++;
            if (p[0] == 'e' && (p[1] == ' ' || p[1] == '\t')) {
                int x, y; sscanf(p + 1, "%d %d", &x, &y);
                if (FIXED[e]) {
                    /* components written '*' are free: parse them as the identity component and remember the mask */
                    char buf[4096], *o = buf; int comp = 0, mask = 0;
                    for (const char *c = vtxt[e]; *c; c++) {
                        if (*c == '|') comp++;
                        if (*c == '*') {
                            const factor *f = &FS[comp]; mask |= 1 << comp;
                            o += sprintf(o, "%s", f->type == F_CYC ? "0" : f->type == F_META ? "0,0" : "1,0,0,1");
                        } else *o++ = *c;
                    }
                    *o = 0;
                    int g = gparse(buf); if (g < 0) { fprintf(stderr, "bad element '%s'\n", vtxt[e]); exit(2); }
                    VOLT[e] = (x == EX[e]) ? g : ginv(g);
                    if (mask) { FIXED[e] = 2; PMASK[e] = mask; }
                }
                e++;
            }
        }
        fclose(fq);
    }
    /* gauge: spanning tree edges that are free -> identity, marked fixed */
    NFREE = 0; FREE = malloc(sizeof(int) * (E + 1));
    int nogauge = getenv("NOGAUGE") ? atoi(getenv("NOGAUGE")) : 0;
    char *intree = calloc(E, 1);
    if (!nogauge) {
        /* prefer tree edges among free edges: BFS using any edges, but fixed edges first so that fixed voltages are respected:
           a spanning tree may contain at most one fixed... simplest: union-find over fixed edges first (their voltages are given,
           and a cycle of fixed edges is fine), then add free edges that join different components; those become identity. */
        int *uf = malloc(sizeof(int) * K); for (int v = 0; v < K; v++) uf[v] = v;
        #define FIND(v) ({ int _v = (v); while (uf[_v] != _v) { uf[_v] = uf[uf[_v]]; _v = uf[_v]; } _v; })
        /* switching (v,g) -> (v, h_v g) changes a_e to h_y a_e h_x^-1; fixed edges need h = 1 at both ends, so all
           their endpoints go into one component before the free spanning forest is chosen */
        int pin = -1;
        for (int e = 0; e < E; e++) if (FIXED[e]) for (int z = 0; z < 2; z++) { int v = z ? EY[e] : EX[e];
            if (pin < 0) pin = v; else { int a = FIND(v), b = FIND(pin); if (a != b) uf[a] = b; } }
        for (int e = 0; e < E; e++) if (!FIXED[e]) { int a = FIND(EX[e]), b = FIND(EY[e]); if (a != b) { uf[a] = b; intree[e] = 1; } }
        free(uf);
    }
    for (int e = 0; e < E; e++) { if (intree[e]) { FIXED[e] = 1; VOLT[e] = IDENT; } else if (FIXED[e] != 1) FREE[NFREE++] = e; }
    free(intree); free(adjn); free(adj); free(fill); free(qu);
}

/* ------------------------------------------------------------------ lift evaluation */
static int **TAB;        /* TAB[e][g] = VOLT[e] * g */
static uint64_t *MSK;    /* K*N masks */
static int *SRC[2], NSRC[2];   /* sources per colour (all base vertices) */
static int D;

static void make_table(int a, int *t) { for (int g = 0; g < N; g++) t[g] = gmul(a, g); }

/* cost with current tables; if col_cb != NULL, report uncovered pairs */
typedef void (*unc_cb)(int src, int v, int g);
static long long evaluate(int **tab, unc_cb cb) {
    long long cost = 0;
    for (int c = 0; c < 2; c++) {
        for (int base = 0; base < NSRC[c]; base += 64) {
            int ns = NSRC[c] - base; if (ns > 64) ns = 64;
            uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
            memset(MSK, 0, sizeof(uint64_t) * (size_t)K * N);
            for (int b = 0; b < ns; b++) MSK[(size_t)SRC[c][base + b] * N + IDENT] |= 1ULL << b;
            for (int l = 1; l <= D; l++) {
                int upd = (c + l) & 1;   /* colour being updated at this level */
                for (int e = 0; e < E; e++) {
                    const int *t = tab[e];
                    uint64_t *X = MSK + (size_t)EX[e] * N, *Y = MSK + (size_t)EY[e] * N;
                    if (upd == 1) { for (int g = 0; g < N; g++) Y[t[g]] |= X[g]; }
                    else { for (int g = 0; g < N; g++) X[g] |= Y[t[g]]; }
                }
            }
            for (int v = 0; v < K; v++) {
                const uint64_t *M = MSK + (size_t)v * N;
                for (int g = 0; g < N; g++) {
                    uint64_t miss = full & ~M[g];
                    if (miss) {
                        cost += __builtin_popcountll(miss);
                        if (cb) while (miss) { int b = __builtin_ctzll(miss); miss &= miss - 1; cb(SRC[c][base + b], v, g); }
                    }
                }
            }
        }
    }
    return cost;
}

/* ------------------------------------------------------------------ search helpers */
static int UCAP = 4096, nunc = 0; static long long seen_unc = 0;
static int *UNC_S, *UNC_V, *UNC_G;
static void collect_cb(int s, int v, int g) {   /* reservoir sample */
    seen_unc++;
    if (nunc < UCAP) { UNC_S[nunc] = s; UNC_V[nunc] = v; UNC_G[nunc] = g; nunc++; }
    else { long long j = rnd() % seen_unc; if (j < UCAP) { UNC_S[j] = s; UNC_V[j] = v; UNC_G[j] = g; } }
}
static int *VADJ, *VADJN;   /* base adjacency: list of edge ids per vertex */
static void build_vadj(void) {
    VADJN = calloc(K + 1, sizeof(int)); VADJ = malloc(sizeof(int) * 2 * E);
    for (int e = 0; e < E; e++) { VADJN[EX[e] + 1]++; VADJN[EY[e] + 1]++; }
    for (int v = 0; v < K; v++) VADJN[v + 1] += VADJN[v];
    int *f = calloc(K, sizeof(int));
    for (int e = 0; e < E; e++) { VADJ[VADJN[EX[e]] + f[EX[e]]++] = e; VADJ[VADJN[EY[e]] + f[EY[e]]++] = e; }
    free(f);
}
/* random walk in the lift of length len from (v,g), not using edge avoid; returns 0 if stuck */
static int lwalk(int *v, int *g, int len, int avoid) {
    for (int s = 0; s < len; s++) {
        int deg = VADJN[*v + 1] - VADJN[*v]; if (deg <= 1 && VADJ[VADJN[*v]] == avoid) return 0;
        int e; do e = VADJ[VADJN[*v] + rnd() % deg]; while (e == avoid);
        if (EX[e] == *v) { *g = gmul(VOLT[e], *g); *v = EY[e]; }
        else { *g = gmul(ginv(VOLT[e]), *g); *v = EX[e]; }
    }
    return 1;
}
static int targeted(int i) {   /* candidate voltage for edge i closing a short path for an uncovered pair */
    if (nunc == 0) return -1;
    int u = rnd() % nunc, s = UNC_S[u], tv = UNC_V[u], tg = UNC_G[u];
    for (int tries = 0; tries < 200; tries++) {
        int a = rnd() % D, b = rnd() % (D - a);
        int v1 = s, g1 = IDENT, v2 = tv, g2 = tg;
        if (!lwalk(&v1, &g1, a, i) || !lwalk(&v2, &g2, b, i)) continue;
        if (v1 == EX[i] && v2 == EY[i]) return gmul(g2, ginv(g1));
        if (v1 == EY[i] && v2 == EX[i]) return gmul(g1, ginv(g2));
    }
    return -1;
}
static int parallel_clash(int i, int a) {   /* another edge with the same ends and the same voltage -> multi-edge in lift */
    for (int j = VADJN[EX[i]]; j < VADJN[EX[i] + 1]; j++) { int e = VADJ[j]; if (e != i && EY[e] == EY[i] && VOLT[e] == a) return 1; }
    return 0;
}
static int simple_ok(void) {
    for (int e = 0; e < E; e++) if (parallel_clash(e, VOLT[e])) return 0;
    return 1;
}

static volatile int stop_flag = 0;
static void on_term(int s) { (void)s; stop_flag = 1; }

static void write_solution(const char *out, long long cost, const char *basefn) {
    FILE *f = fopen(out, "w"); if (!f) { perror(out); return; }
    fprintf(f, "# lift solution: base %s\n", basefn);
    fprintf(f, "lift D %d Delta %d k %d N %d n %lld cost %lld\n", D, MAXDEG, K, N, (long long)K * N, cost);
    fprintf(f, "group %s\n", GSPEC);
    fprintf(f, "k %d\n", K);
    for (int e = 0; e < E; e++) { char b[512]; gdesc(VOLT[e], b); fprintf(f, "e %d %d = %s\n", EX[e], EY[e], b); }
    fclose(f);
}

/* ------------------------------------------------------------------ exact check */
static int check_solution(const char *sol, const char *edges_out) {
    /* read "group ..." line */
    FILE *fp = fopen(sol, "r"); if (!fp) { perror(sol); return 2; }
    char line[4096], gl[4096] = ""; int Dd = -1;
    while (fgets(line, sizeof line, fp)) {
        if (!strncmp(line, "group ", 6)) strcpy(gl, line + 6);
        if (!strncmp(line, "lift ", 5)) sscanf(line, "lift D %d", &Dd);
    }
    fclose(fp);
    if (!gl[0]) die("solution: no group line");
    char *tok[64]; int nt = 0; for (char *p = strtok(gl, " \t\n"); p && nt < 64; p = strtok(NULL, " \t\n")) tok[nt++] = p;
    int a = 0; parse_group(nt, tok, &a);
    setenv("NOGAUGE", "1", 1);
    read_base(sol, 1);
    long long n = (long long)K * N;
    printf("check %s: group %s (N=%d), base k=%d E=%d, lift n=%lld\n", sol, GSPEC, N, K, E, n);
    for (int e = 0; e < E; e++) if (!FIXED[e]) die("solution has an edge without voltage");
    /* adjacency of the lift */
    int deg = 0, mindeg = 1 << 30;
    for (int v = 0; v < K; v++) { if (DEG[v] > deg) deg = DEG[v]; if (DEG[v] < mindeg) mindeg = DEG[v]; }
    build_vadj();
    printf("base degrees: min %d max %d; lift simple (no parallel equal voltages): %s\n", mindeg, deg, simple_ok() ? "yes" : "NO");
    int **tf = malloc(sizeof(int *) * E), **ti = malloc(sizeof(int *) * E);
    for (int e = 0; e < E; e++) { tf[e] = malloc(sizeof(int) * N); ti[e] = malloc(sizeof(int) * N); make_table(VOLT[e], tf[e]); for (int g = 0; g < N; g++) ti[e][tf[e][g]] = g; }
    int *dist = malloc(sizeof(int) * n), *qu = malloc(sizeof(int) * n);
    int diam = 0, unreached = 0;
    for (int s = 0; s < K; s++) {
        for (long long i = 0; i < n; i++) dist[i] = -1;
        long long h = 0, t = 0; long long src = (long long)s * N + IDENT; dist[src] = 0; qu[t++] = (int)src;
        int ecc = 0;
        while (h < t) {
            int x = qu[h++], v = x / N, g = x % N;
            for (int j = VADJN[v]; j < VADJN[v + 1]; j++) {
                int e = VADJ[j]; long long y;
                if (EX[e] == v) y = (long long)EY[e] * N + tf[e][g]; else y = (long long)EX[e] * N + ti[e][g];
                if (dist[y] < 0) { dist[y] = dist[x] + 1; if (dist[y] > ecc) ecc = dist[y]; qu[t++] = (int)y; }
            }
        }
        if (t < n) unreached += (int)(n - t);
        if (ecc > diam) diam = ecc;
        printf("  ecc(%d,e) = %d%s\n", s, ecc, t < n ? " (not all reached)" : "");
    }
    printf("RESULT n=%lld Delta=%d diameter=%d%s\n", n, deg, diam, unreached ? " DISCONNECTED" : "");
    if (Dd >= 0) printf("target D=%d: %s\n", Dd, (!unreached && diam <= Dd && simple_ok()) ? "VALID" : "INVALID");
    if (edges_out) {
        FILE *fo = fopen(edges_out, "w");
        fprintf(fo, "%lld\n", n);
        for (int e = 0; e < E; e++) for (int g = 0; g < N; g++) fprintf(fo, "%lld %lld\n", (long long)EX[e] * N + g, (long long)EY[e] * N + tf[e][g]);
        fclose(fo); printf("wrote %s\n", edges_out);
    }
    return (!unreached && (Dd < 0 || diam <= Dd)) ? 0 : 1;
}

/* ------------------------------------------------------------------ main */
static void setup_eval(void) {
    build_vadj();
    TAB = malloc(sizeof(int *) * E);
    for (int e = 0; e < E; e++) { TAB[e] = malloc(sizeof(int) * N); make_table(VOLT[e], TAB[e]); }
    MSK = malloc(sizeof(uint64_t) * (size_t)K * N);
    for (int c = 0; c < 2; c++) { SRC[c] = malloc(sizeof(int) * K); NSRC[c] = 0; }
    for (int v = 0; v < K; v++) SRC[COL[v]][NSRC[COL[v]]++] = v;
    UNC_S = malloc(sizeof(int) * UCAP); UNC_V = malloc(sizeof(int) * UCAP); UNC_G = malloc(sizeof(int) * UCAP);
}
static int restrict_volt(int e, int x) {
    if (FIXED[e] != 2) return x;
    int z = 0;
    for (int i = 0; i < nf; i++) { int c = (PMASK[e] >> i) & 1 ? x : VOLT[e]; z += ((c / RAD[i]) % FS[i].n) * RAD[i]; }
    return z;
}
static int random_volt(int i) { int x, t = 0; do { x = restrict_volt(i, rnd() % N); t++; } while (parallel_clash(i, x) && t < 1000); return x; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: lift search|check|sample ... (see source header)\n"); return 2; }
    if (!strcmp(argv[1], "check")) { if (argc < 3) die("lift check SOL [EDGES]"); return check_solution(argv[2], argc > 3 ? argv[3] : NULL); }
    int sample = !strcmp(argv[1], "sample");
    if (!sample && strcmp(argv[1], "search")) die("mode must be search, check or sample");
    if (sample ? argc < 6 : argc < 9) die("not enough arguments");
    const char *basefn = argv[2]; D = atoi(argv[3]);
    double secs = 0; int K2 = 1, M = 0; const char *out = NULL; int a;
    if (sample) { M = atoi(argv[4]); a = 5; }
    else { secs = atof(argv[4]); rs ^= ((uint64_t)atoll(argv[5]) + 1) * 0x9E3779B97F4A7C15ULL; for (int t = 0; t < 10; t++) rnd(); K2 = atoi(argv[6]); out = argv[7]; a = 8; }
    if (getenv("SEED")) { rs ^= ((uint64_t)atoll(getenv("SEED")) + 7) * 0xD1B54A32D192ED03ULL; for (int t = 0; t < 10; t++) rnd(); }
    parse_group(argc, argv, &a);
    read_base(basefn, 0);
    if (getenv("UCAP")) UCAP = atoi(getenv("UCAP"));
    setup_eval();
    fprintf(stderr, "base %s: k=%d E=%d Delta=%d free=%d; group %s N=%d; lift n=%lld; D=%d\n", basefn, K, E, MAXDEG, NFREE, GSPEC, N, (long long)K * N, D);
    for (int j = 0; j < NFREE; j++) { int e = FREE[j]; VOLT[e] = random_volt(e); make_table(VOLT[e], TAB[e]); }
    if (sample) {
        long long *v = malloc(sizeof(long long) * M); double t0 = now();
        for (int t = 0; t < M; t++) {
            for (int j = 0; j < NFREE; j++) { int e = FREE[j]; VOLT[e] = random_volt(e); make_table(VOLT[e], TAB[e]); }
            v[t] = evaluate(TAB, NULL);
        }
        for (int i = 1; i < M; i++) { long long key = v[i]; int j = i - 1; while (j >= 0 && v[j] > key) { v[j + 1] = v[j]; j--; } v[j + 1] = key; }
        printf("SAMPLE base=%s D=%d group=%s N=%d n=%lld samples=%d min=%lld p10=%lld median=%lld (%.3f ms/eval)\n", basefn, D, GSPEC, N, (long long)K * N, M, v[0], v[M / 10], v[M / 2], 1e3 * (now() - t0) / M);
        return 0;
    }
    if (NFREE == 0) die("no free edges");
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 1.5, TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.15;
    double COOL = getenv("COOL") ? atof(getenv("COOL")) : 20, REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 60;
    double REPORT = getenv("REPORT") ? atof(getenv("REPORT")) : 30;
    int TARGP = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
    signal(SIGTERM, on_term); signal(SIGINT, on_term);
    int *cand = malloc(sizeof(int) * K2), **ctab = malloc(sizeof(int *) * K2); long long *cc = malloc(sizeof(long long) * K2);
    for (int t = 0; t < K2; t++) ctab[t] = malloc(sizeof(int) * N);
    int *bestV = malloc(sizeof(int) * E);
    nunc = 0; seen_unc = 0; long long c = evaluate(TAB, collect_cb), best = c; memcpy(bestV, VOLT, sizeof(int) * E);
    double t0 = now(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0; long long evals = 1, steps = 0;
    fprintf(stderr, "start cost=%lld\n", c);
    while (!stop_flag && now() - t0 < secs && best > 0) {
        int i = FREE[rnd() % NFREE], old = VOLT[i];
        for (int t = 0; t < K2; t++) {
            int x = ((int)(rnd() % 100) < TARGP) ? targeted(i) : -1;
            if (x >= 0) x = restrict_volt(i, x);
            if (x < 0 || x == old || parallel_clash(i, x)) { int tr = 0; do { x = restrict_volt(i, rnd() % N); tr++; } while ((x == old || parallel_clash(i, x)) && tr < 1000); }
            cand[t] = x;
            make_table(x, ctab[t]);
            int *keep = TAB[i]; TAB[i] = ctab[t]; cc[t] = evaluate(TAB, NULL); TAB[i] = keep;
        }
        evals += K2;
        int bt = 0; for (int t = 1; t < K2; t++) if (cc[t] < cc[bt]) bt = t;
        if (cc[bt] <= c || exp((double)(c - cc[bt]) / T) > (rnd() % 1000000) / 1e6) {
            VOLT[i] = cand[bt]; int *tmp = TAB[i]; TAB[i] = ctab[bt]; ctab[bt] = tmp;
            nunc = 0; seen_unc = 0; c = evaluate(TAB, collect_cb); evals++;
        }
        steps++;
        if (c < best) { best = c; memcpy(bestV, VOLT, sizeof(int) * E); lastimp = now(); }
        T = TMAX * pow(0.5, (now() - lastheat) / COOL); if (T < TMIN) T = TMIN;
        if (now() - lastimp > REHEAT) {
            lastheat = now(); T = TMAX; memcpy(VOLT, bestV, sizeof(int) * E);
            for (int e = 0; e < E; e++) make_table(VOLT[e], TAB[e]);
            nunc = 0; seen_unc = 0; c = evaluate(TAB, collect_cb); lastimp = now();
        }
        if (now() - lastprint > REPORT) { fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%lld best=%lld T=%.2f\n", now() - t0, steps, evals, c, best, T); lastprint = now(); }
    }
    memcpy(VOLT, bestV, sizeof(int) * E);
    for (int e = 0; e < E; e++) make_table(VOLT[e], TAB[e]);
    long long fin = evaluate(TAB, NULL);
    printf("RESULT base=%s D=%d Delta=%d k=%d group=%s N=%d n=%lld best=%lld evals=%lld time=%.1f\n", basefn, D, MAXDEG, K, GSPEC, N, (long long)K * N, fin, evals, now() - t0);
    if (fin == 0 && simple_ok()) { write_solution(out, fin, basefn); printf("wrote %s\n", out); }
    else if (getenv("WRITEBEST")) write_solution(out, fin, basefn);
    return fin == 0 ? 0 : 1;
}
