/* prodopt5.c: exhaustive 1-opt of Haar graphs H(G,S), G = PSL(2,p) x (Z_m x|_r Z_k)  (p = 0: no PSL factor).
 * Haar graph: vertices (g,A) = g, (g,B) = N + g; edges (g,A) ~ (s g,B) for s in S.  Right multiplication is an
 * automorphism, so BFS from (e,A) gives the cost; cost (D even, as haar_gen3): number of B-side vertices at distance
 * > D-1 from (e,A) (unreached included).  Cost 0 is then checked fully (ecc from (e,A) and (e,B) at most D, all vertices).
 *
 * usage: prodopt5 p m k r STATEFILE PROGFILE SECONDS OUTPREFIX
 *   STATEFILE: solution-format file (header "d D spec ... N n", then d lines "idx desc z=0"; desc = prod[mat;meta] or meta).
 *   Slot 0 (identity) is kept; slots 1..d-1 are replaced by every candidate t (exhaustive), resuming from PROGFILE.
 *   Writes OUTPREFIX.cands (every candidate with cost <= 1: slot t cost) and OUTPREFIX_sol_<n>.txt for cost 0 that
 *   pass the full check.  PROGFILE holds the next candidate number c (slot = 1 + c / N, t = c % N).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define D 10
static int p, P, m, k, M, N, d;
static int64_t *R;
static int *PT, *PIv;          /* PSL mult table and inverse, P x P and P */
static int *mindex;            /* p^4 -> element index (all det-1 keys) */
static int *matkey;            /* element index -> key a*p^3+b*p^2+c*p+d (canonical) */
static int32_t *Fw, *Bw;       /* [g*d + i]: s_i g and s_i^{-1} g */
static int S[64];
static uint8_t *dist;
static int32_t *Q;

static int canon(int key) {
    int a = key / (p * p * p), b = key / (p * p) % p, c = key / p % p, dd = key % p;
    int na = (p - a) % p, nb = (p - b) % p, nc = (p - c) % p, nd = (p - dd) % p;
    int k2 = ((na * p + nb) * p + nc) * p + nd;
    return key < k2 ? key : k2;
}

static void build_psl(void) {
    int p4 = p * p * p * p;
    int *canidx = malloc(sizeof(int) * p4);
    mindex = malloc(sizeof(int) * p4);
    for (int i = 0; i < p4; i++) { canidx[i] = -1; mindex[i] = -1; }
    matkey = malloc(sizeof(int) * p4);
    int n = 0;
    for (int key = 0; key < p4; key++) {
        int a = key / (p * p * p), b = key / (p * p) % p, c = key / p % p, dd = key % p;
        if ((((a * dd - b * c) % p) + p) % p != 1) continue;
        if (canon(key) == key) { canidx[key] = n; matkey[n] = key; n++; }
    }
    for (int key = 0; key < p4; key++) {
        int a = key / (p * p * p), b = key / (p * p) % p, c = key / p % p, dd = key % p;
        if ((((a * dd - b * c) % p) + p) % p != 1) continue;
        mindex[key] = canidx[canon(key)];
    }
    P = n;
    PT = malloc(sizeof(int) * P * P);
    PIv = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) {
        int key = matkey[i];
        int a = key / (p * p * p), b = key / (p * p) % p, c = key / p % p, dd = key % p;
        /* inverse = adj = [[d,-b],[-c,a]] */
        PIv[i] = mindex[((dd * p + (p - b) % p) * p + (p - c) % p) * p + a];
        for (int j = 0; j < P; j++) {
            int k2 = matkey[j];
            int e = k2 / (p * p * p), f = k2 / (p * p) % p, g = k2 / p % p, h = k2 % p;
            int x0 = (a * e + b * g) % p, x1 = (a * f + b * h) % p, x2 = (c * e + dd * g) % p, x3 = (c * f + dd * h) % p;
            PT[i * P + j] = mindex[((x0 * p + x1) * p + x2) * p + x3];
        }
    }
    free(canidx);
}

static inline int gmul(int g1, int g2) {
    int p1 = g1 / M, x1 = g1 % M, p2 = g2 / M, x2 = g2 % M;
    int a1 = x1 / k, j1 = x1 % k, a2 = x2 / k, j2 = x2 % k;
    int a = (int)((a1 + R[j1] * a2) % m);
    int j = (j1 + j2) % k;
    return PT[p1 * P + p2] * M + a * k + j;
}
static inline int ginv(int g) {
    int pi = g / M, x = g % M, a = x / k, j = x % k;
    int jj = (k - j) % k;
    int b = (int)((m - (R[jj] * a) % m) % m);
    return PIv[pi] * M + b * k + jj;
}
static int E;                  /* identity element index */

static int *gPi, *gA, *gJ;      /* components of every group element */
static int *mulR;               /* scratch: mulR[x] = R[j] x mod m */
static void build_slot(int i, int t) {  /* fill Fw/Bw column i for generator t (no division in the loop) */
    int ti = ginv(t);
    for (int pass = 0; pass < 2; pass++) {
        int s = pass == 0 ? t : ti;
        int sp = s / M, sx = s % M, sa = sx / k, sj = sx % k;
        const int *PTrow = PT + sp * P;
        for (int x = 0; x < m; x++) mulR[x] = (int)((R[sj] * x) % m);
        int32_t *col = pass == 0 ? Fw : Bw;
        for (int g = 0; g < N; g++) {
            int pg = gPi[g], ag = gA[g], jg = gJ[g];
            int a2 = sa + mulR[ag]; if (a2 >= m) a2 -= m;
            int j2 = sj + jg; if (j2 >= k) j2 -= k;
            col[(size_t)g * d + i] = (PTrow[pg] * M) + a2 * k + j2;
        }
    }
}

/* BFS from src over 2N vertices; dist[v] = 255 if unreached. */
static void bfs(int src) {
    int V = 2 * N;
    memset(dist, 255, V);
    int qh = 0, qt = 0;
    Q[qt++] = src; dist[src] = 0;
    while (qh < qt) {
        int v = Q[qh++];
        int dv = dist[v] + 1;
        if (v < N) {                           /* (g,A) -> (s g,B) */
            const int32_t *row = Fw + (size_t)v * d;
            for (int i = 0; i < d; i++) { int u = N + row[i]; if (dist[u] == 255) { dist[u] = dv; Q[qt++] = u; } }
        } else {                               /* (h,B) -> (s^-1 h,A) */
            const int32_t *row = Bw + (size_t)(v - N) * d;
            for (int i = 0; i < d; i++) { int u = row[i]; if (dist[u] == 255) { dist[u] = dv; Q[qt++] = u; } }
        }
    }
}

static int cost_of(void) {          /* D even: B-side vertices not within D-1 of (e,A) */
    bfs(E);
    int c = 0;
    for (int v = N; v < 2 * N; v++) if (dist[v] > D - 1) c++;
    return c;
}

static int full_check(void) {       /* all vertices within D from (e,A) and from (e,B) */
    for (int s = 0; s < 2; s++) {
        bfs(s == 0 ? E : N + E);
        for (int v = 0; v < 2 * N; v++) if (dist[v] > D) return 0;
    }
    return 1;
}

static void parse_elem(const char *s, int *g) {
    int a, b, c, dd, aa, jj;
    const char *q = strstr(s, "mat(");
    int pi = 0;
    if (q) {
        if (sscanf(q, "mat(%d,%d,%d,%d)", &a, &b, &c, &dd) != 4) { fprintf(stderr, "bad mat in %s\n", s); exit(2); }
        pi = mindex[((((a % p + p) % p) * p + ((b % p + p) % p)) * p + ((c % p + p) % p)) * p + ((dd % p + p) % p)];
    }
    const char *z = strstr(s, "meta(");
    if (z) { if (sscanf(z, "meta(a=%d,j=%d)", &aa, &jj) != 2) { fprintf(stderr, "bad meta in %s\n", s); exit(2); } }
    else { aa = 0; jj = 0; }
    *g = pi * M + aa * k + jj;
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void write_solution(const char *path, int cost) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    if (p > 0) fprintf(f, "%d %d prod psl %d meta %d %d %lld n 1 N %d cost %d\n", d, D, p, m, k, (long long)R[1], N, cost);
    else fprintf(f, "%d %d meta %d %d %lld n 1 N %d cost %d\n", d, D, m, k, (long long)R[1], N, cost);
    for (int i = 0; i < d; i++) {
        int g = S[i], pi = g / M, x = g % M, aa = x / k, jj = x % k;
        if (p > 0) {
            int key = matkey[pi];
            int a = key / (p * p * p), b = key / (p * p) % p, c = key / p % p, dd = key % p;
            fprintf(f, "%d prod[mat(%d,%d,%d,%d);meta(a=%d,j=%d)] z=0\n", g, a, b, c, dd, aa, jj);
        } else fprintf(f, "%d meta(a=%d,j=%d) z=0\n", g, aa, jj);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: prodopt5 p m k r STATEFILE PROGFILE SECONDS OUTPREFIX\n"); return 2; }
    p = atoi(argv[1]); m = atoi(argv[2]); k = atoi(argv[3]);
    long long r = atoll(argv[4]);
    const char *statef = argv[5], *progf = argv[6];
    double secs = atof(argv[7]); const char *outp = argv[8];
    if (p > 0) build_psl(); else { P = 1; PT = malloc(sizeof(int)); PT[0] = 0; PIv = malloc(sizeof(int)); PIv[0] = 0; matkey = malloc(sizeof(int)); matkey[0] = 0; }
    M = m * k;
    R = malloc(sizeof(int64_t) * k); R[0] = 1 % m;
    for (int j = 1; j < k; j++) R[j] = R[j - 1] * r % m;
    if (R[k - 1] * r % m != 1 % m) { fprintf(stderr, "r^k != 1\n"); return 2; }
    N = P * M;

    /* read state */
    FILE *sf = fopen(statef, "r");
    if (!sf) { fprintf(stderr, "no state\n"); return 2; }
    char line[4096];
    if (!fgets(line, sizeof line, sf)) return 2;
    if (sscanf(line, "%d", &d) != 1) return 2;
    int got = 0;
    while (got < d && fgets(line, sizeof line, sf)) {
        char *sp = strchr(line, ' ');
        if (!sp) continue;
        int g; parse_elem(sp + 1, &g);
        S[got++] = g;
    }
    fclose(sf);
    if (got != d) { fprintf(stderr, "short state\n"); return 2; }

    gPi = malloc(sizeof(int) * N); gA = malloc(sizeof(int) * N); gJ = malloc(sizeof(int) * N); mulR = malloc(sizeof(int) * m);
    for (int g = 0; g < N; g++) { gPi[g] = g / M; int x = g % M; gA[g] = x / k; gJ[g] = x % k; }
    Fw = malloc(sizeof(int32_t) * (size_t)N * d);
    Bw = malloc(sizeof(int32_t) * (size_t)N * d);
    dist = malloc(2 * N);
    Q = malloc(sizeof(int32_t) * 2 * N);
    for (int i = 0; i < d; i++) build_slot(i, S[i]);
    E = (p > 0) ? mindex[p * p * p + 1] * M : 0;
    int base = cost_of();
    fprintf(stderr, "N=%d d=%d base cost=%d (identity S[0]=%d)\n", N, d, base, S[0]);

    if (getenv("WRITEBASE")) { char bp[1100]; snprintf(bp, sizeof bp, "%s_base.txt", outp); write_solution(bp, base); }
    int il = getenv("IL") != NULL;
    long long c0 = 0;
    { FILE *pf = fopen(progf, "r"); if (pf) { if (fscanf(pf, "%lld", &c0) != 1) c0 = 0; fclose(pf); } }
    long long total = (long long)(d - 1) * N;
    if (getenv("IL")) total = (long long)(d - 1) * N;
    char candpath[1024], line2[1024];
    snprintf(candpath, sizeof candpath, "%s.cands", outp);
    FILE *cf = fopen(candpath, "a");
    long long hist[4] = {0, 0, 0, 0}; long long nskip = 0, nev = 0;
    double t0 = now();
    long long c = c0;
    int best = 1 << 30;
    for (; c < total; c++) {
        if ((c & 63) == 0 && now() - t0 > secs) break;
        int slot, t;
        if (il) { slot = 1 + (int)(c % (d - 1)); t = (int)(c / (d - 1)); }   /* interleave slots: uniform coverage */
        else { slot = 1 + (int)(c / N); t = (int)(c % N); }
        int skip = (t == S[slot]);
        for (int i = 0; i < d && !skip; i++) if (i != slot && S[i] == t) skip = 1;
        if (skip) { nskip++; continue; }
        int old = S[slot];
        S[slot] = t;
        build_slot(slot, t);
        int cost = cost_of();
        nev++;
        if (cost < 4) hist[cost]++;
        if (cost < best) best = cost;
        if (cost <= 1 && cf) {
            fprintf(cf, "slot %d t %d cost %d\n", slot, t, cost);
            fflush(cf);
        }
        if (cost == 0) {
            int ok = full_check();
            snprintf(line2, sizeof line2, "%s_sol_%lld.txt", outp, c);
            write_solution(line2, 0);
            fprintf(stderr, "COST0 candidate c=%lld slot=%d t=%d full_check=%d file=%s\n", c, slot, t, ok, line2);
            if (cf) { fprintf(cf, "COST0 slot %d t %d full_check %d file %s\n", slot, t, ok, line2); fflush(cf); }
        }
        S[slot] = old;
        build_slot(slot, old);
    }
    if (cf) fclose(cf);
    FILE *pf = fopen(progf, "w");
    if (pf) { fprintf(pf, "%lld\n", c); fclose(pf); }
    fprintf(stderr, "chunk c=%lld..%lld evals=%lld skipped=%lld hist(cost0,1,2,3)=%lld,%lld,%lld,%lld best=%d time=%.1f next=%lld of %lld\n",
            c0, c, nev, nskip, hist[0], hist[1], hist[2], hist[3], best, now() - t0, c, total);
    return 0;
}
