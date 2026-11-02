/* b06: Haar graphs H(G,S), G = H x H x H, alpha(a,b,c) = (c,a,b) (order 3).
 * Vertices A(g), B(g), g in G (N = |H|^3). Edges A(g) ~ B(s g), s in S, |S| = 4, S = {e} + stuff.
 * D = 12: a BFS from A(e) decides the diameter. cost = #B not reached within 11 + #A not reached within 12.
 * Usage: h3shift TABLE MODE NSAMP SEED OUTPREFIX
 *   MODE = orbit : exhaustive scan of S = {e, x, ax, a^2x}, x not alpha-fixed, x = min of its orbit
 *   MODE = rand  : NSAMP plain random S = {e, x, y, z} (no orbit structure), for comparison
 *   MODE = orbitrand : NSAMP random orbit samples
 * Writes OUTPREFIX.edges (first line n = 2N, then "u v") when a cost-0 S is found.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int h, N, hh;
static int *M, *INV;
static int *dist, *queue;
static int *alphaP;

static int *CA, *CB, *CC; /* coordinates of each element */
static int *EPS; /* optional abelian character of H into Z2 (FILTER) */
static inline int mulG(int s1, int s2, int s3, int g) {
    return M[s1 * h + CA[g]] * hh + M[s2 * h + CB[g]] * h + M[s3 * h + CC[g]];
}

static int read_table(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(1); }
    if (fscanf(f, "%d", &h) != 1) exit(1);
    M = malloc(sizeof(int) * h * h);
    INV = malloc(sizeof(int) * h);
    for (int i = 0; i < h * h; i++) if (fscanf(f, "%d", &M[i]) != 1) exit(1);
    fclose(f);
    for (int x = 0; x < h; x++) {
        INV[x] = -1;
        for (int y = 0; y < h; y++) if (M[x * h + y] == 0) INV[x] = y;
        if (INV[x] < 0) { fprintf(stderr, "no inverse\n"); exit(1); }
    }
    hh = h * h;
    N = hh * h;
    return 0;
}

static inline int alpha(int g) {
    int a = g / hh, rem = g - a * hh, b = rem / h, c = rem - b * h;
    return c * hh + a * h + b; /* (a,b,c) -> (c,a,b) */
}

/* S given as k elements of G (S[0] must be identity 0). */
static int cost_of(const int *S, int ns, int *costB, int *costA, int *maxd) {
    int sc[8][3], si[8][3];
    for (int k = 0; k < ns; k++) {
        int s = S[k];
        int a = s / hh, rem = s - a * hh, b = rem / h, c = rem - b * h;
        sc[k][0] = a; sc[k][1] = b; sc[k][2] = c;
        si[k][0] = INV[a]; si[k][1] = INV[b]; si[k][2] = INV[c];
    }
    for (int i = 0; i < 2 * N; i++) dist[i] = -1;
    int qh = 0, qt = 0;
    dist[0] = 0; queue[qt++] = 0;
    int mx = 0;
    while (qh < qt) {
        int u = queue[qh++];
        int du = dist[u];
        if (u < N) {
            for (int k = 0; k < ns; k++) {
                int v = N + mulG(sc[k][0], sc[k][1], sc[k][2], u);
                if (dist[v] < 0) { dist[v] = du + 1; queue[qt++] = v; if (du + 1 > mx) mx = du + 1; }
            }
        } else {
            int hb = u - N;
            for (int k = 0; k < ns; k++) {
                int v = mulG(si[k][0], si[k][1], si[k][2], hb);
                if (dist[v] < 0) { dist[v] = du + 1; queue[qt++] = v; if (du + 1 > mx) mx = du + 1; }
            }
        }
    }
    int cb = 0, ca = 0;
    for (int i = N; i < 2 * N; i++) if (dist[i] < 0 || dist[i] > 11) cb++;
    for (int i = 0; i < N; i++) if (dist[i] < 0 || dist[i] > 12) ca++;
    *costB = cb; *costA = ca; *maxd = mx;
    return cb + ca;
}

static void write_edges(const char *fn, const int *S, int ns) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "%d\n", 2 * N);
    for (int g = 0; g < N; g++)
        for (int k = 0; k < ns; k++) {
            int s = S[k];
            int a = s / hh, rem = s - a * hh, b = rem / h, c = rem - b * h;
            fprintf(f, "%d %d\n", g, N + mulG(a, b, c, g));
        }
    fclose(f);
}

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: TABLE MODE NSAMP SEED OUTPREFIX\n"); return 1; }
    read_table(argv[1]);
    const char *mode = argv[2];
    long nsamp = atol(argv[3]);
    rs = 88172645463325252ULL ^ (uint64_t)atol(argv[4]) * 2654435761ULL;
    const char *outp = argv[5];
    dist = malloc(sizeof(int) * 2 * N);
    queue = malloc(sizeof(int) * 2 * N);
    alphaP = malloc(sizeof(int) * N);
    CA = malloc(sizeof(int) * N); CB = malloc(sizeof(int) * N); CC = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) { CA[g] = g / hh; int rem = g - CA[g] * hh; CB[g] = rem / h; CC[g] = rem - CB[g] * h; }
    int filt = 0;
    if (getenv("EPSFILE")) {
        EPS = malloc(sizeof(int) * h); FILE *ef = fopen(getenv("EPSFILE"), "r");
        for (int i = 0; i < h; i++) if (fscanf(ef, "%d", &EPS[i]) != 1) exit(1);
        fclose(ef); filt = 1;
    }
    int xlo = getenv("XLO") ? atoi(getenv("XLO")) : 1, xhi = getenv("XHI") ? atoi(getenv("XHI")) : N - 1;
    for (int g = 0; g < N; g++) alphaP[g] = alpha(g);
    fprintf(stderr, "h=%d N=%d 2N=%d\n", h, N, 2 * N);

    int best = 1 << 30, bestS[4] = {0, 0, 0, 0};
    long hist[1000];
    memset(hist, 0, sizeof(hist));
    int S[4];
    int cb, ca, md;
    S[0] = 0;

    if (strcmp(mode, "orbit") == 0) {
        long n = 0, nfix = 0;
        long cnt0 = 0;
        for (int x = xlo; x < xhi && x < N; x++) {
            int ax = alphaP[x], a2x = alphaP[ax];
            if (ax == x) { nfix++; continue; }
            if (!(x < ax && x < a2x)) continue;
            if (filt) { /* connectivity needs eps(x), eps(alpha x), eps(alpha^2 x) to span Z2^3: weight-1 eps(x) */
                int w = EPS[CA[x]] + EPS[CB[x]] + EPS[CC[x]];
                if (w != 1) continue;
            }
            S[1] = x; S[2] = ax; S[3] = a2x;
            int c = cost_of(S, 4, &cb, &ca, &md);
            n++;
            hist[c < 999 ? c : 999]++;
            if (c == 0) cnt0++;
            if (c < best) { best = c; memcpy(bestS, S, sizeof(S)); fprintf(stderr, "new best %d at x=%d (B %d A %d maxd %d)\n", c, x, cb, ca, md); }
            if (c == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s_x%d.edges", outp, x);
                write_edges(fn, S, 4);
                printf("VALID cost 0 x=%d file %s\n", x, fn);
            }
        }
        printf("orbits scanned %ld, fixed skipped %ld, cost0 count %ld, best %d\n", n, nfix, cnt0, best);
    } else if (strcmp(mode, "rand") == 0 || strcmp(mode, "orbitrand") == 0) {
        int orb = strcmp(mode, "orbitrand") == 0;
        for (long t = 0; t < nsamp; t++) {
            int x, y, z;
            if (orb) {
                do { x = 1 + rnd() % (N - 1); } while (alphaP[x] == x);
                S[1] = x; S[2] = alphaP[x]; S[3] = alphaP[S[2]];
                if (S[1] == S[2] || S[1] == S[3] || S[2] == S[3] || S[1] == 0) { t--; continue; }
            } else {
                do { x = 1 + rnd() % (N - 1); y = 1 + rnd() % (N - 1); z = 1 + rnd() % (N - 1); }
                while (x == y || x == z || y == z);
                S[1] = x; S[2] = y; S[3] = z;
            }
            int c = cost_of(S, 4, &cb, &ca, &md);
            hist[c < 999 ? c : 999]++;
            if (c < best) { best = c; memcpy(bestS, S, sizeof(S)); }
            if (c == 0) {
                char fn[512]; snprintf(fn, sizeof fn, "%s_%ld.edges", outp, t);
                write_edges(fn, S, 4);
                printf("VALID cost 0 S={%d,%d,%d,%d} file %s\n", S[0], S[1], S[2], S[3], fn);
            }
        }
    }
    printf("histogram of cost (count), first 40 buckets:\n");
    for (int c = 0; c < 40; c++) if (hist[c]) printf("  cost %d: %ld\n", c, hist[c]);
    printf("best cost %d S={%d,%d,%d,%d}\n", best, bestS[0], bestS[1], bestS[2], bestS[3]);
    return 0;
}
