/* c8 (round r1-d11D5): exact edge-criticality of the (11,5) record graph, plus a
   twin-vertex augmentation test.
   Build: gcc -O2 -o augment augment.c
   Usage: augment EDGES stats
          augment EDGES twin TRIALS SEED
   Criticality rule: deleting e=(p,c) (c child of p in the BFS DAG from source x) changes
   distances from x only if p is the UNIQUE parent of c. Only those sources are repaired locally. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define DEG 11
#define INFD 200
#define DIAM 5

static int n, m;
static int *eu, *ev, *nb, *dg, *col;
static uint8_t *DIST, *PC;
static uint16_t *UP;
static int *aff, *evald, *nd, *Slist;
static int stamp = 0;

static void die(const char *s) { fprintf(stderr, "%s\n", s); exit(1); }

static void read_graph(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) die("open edges");
    if (fscanf(f, "%d", &n) != 1) die("header");
    int cap = n * DEG / 2 + 16;
    eu = malloc(sizeof(int) * cap); ev = malloc(sizeof(int) * cap); m = 0;
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (m == cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        eu[m] = a; ev[m] = b; m++;
    }
    fclose(f);
    nb = malloc(sizeof(int) * (size_t)n * DEG); dg = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) {
        a = eu[i]; b = ev[i];
        if (dg[a] >= DEG || dg[b] >= DEG) die("degree above 11");
        nb[a * DEG + dg[a]++] = b; nb[b * DEG + dg[b]++] = a;
    }
}

static void colour_and_check(void) {
    col = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) col[i] = -1;
    int *q = malloc(sizeof(int) * n); int h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) {
        int x = q[h++];
        for (int j = 0; j < dg[x]; j++) {
            int y = nb[x * DEG + j];
            if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; }
            else if (col[y] == col[x]) bip = 0;
        }
    }
    int regular = 1; for (int i = 0; i < n; i++) if (dg[i] != DEG) regular = 0;
    int na = 0; for (int i = 0; i < n; i++) if (col[i] == 0) na++;
    printf("n=%d edges=%d regular11=%d bipartite=%d connected=%d |A|=%d |B|=%d\n",
           n, m, regular, bip, t == n, na, n - na);
    free(q);
}

static void build_dist(void) {
    DIST = malloc((size_t)n * n);
    int *q = malloc(sizeof(int) * n); int maxd = 0;
    for (int x = 0; x < n; x++) {
        uint8_t *Dx = DIST + (size_t)x * n;
        memset(Dx, 255, n); Dx[x] = 0;
        int h = 0, t = 0; q[t++] = x;
        while (h < t) {
            int y = q[h++];
            for (int j = 0; j < dg[y]; j++) { int w = nb[y * DEG + j]; if (Dx[w] == 255) { Dx[w] = Dx[y] + 1; q[t++] = w; } }
        }
        if (t != n) die("base graph disconnected");
        for (int y = 0; y < n; y++) if (Dx[y] > maxd) maxd = Dx[y];
    }
    printf("base diameter=%d\n", maxd);
    free(q);
}

/* PC[v*n+x] = number of BFS-DAG parents of v from source x; UP = the parent when that number is 1 */
static void build_parents(void) {
    PC = calloc((size_t)n * n, 1); UP = calloc((size_t)n * n, sizeof(uint16_t));
    for (int x = 0; x < n; x++) {
        const uint8_t *Dx = DIST + (size_t)x * n;
        for (int v = 0; v < n; v++) {
            int c = 0, up = 0;
            if (v != x)
                for (int j = 0; j < dg[v]; j++) { int w = nb[v * DEG + j]; if (Dx[w] + 1 == Dx[v]) { c++; up = w; } }
            PC[(size_t)v * n + x] = (uint8_t)(c > 255 ? 255 : c);
            UP[(size_t)v * n + x] = (uint16_t)up;
        }
    }
}

/* Source x; edge (p,c) with D_x[c] = D_x[p]+1 and c's unique parent p. Returns 1 if all distances
   from x stay <= DIAM after deleting (p,c). Affected set = vertices all of whose parents are affected. */
static int src_core(int x, int p, int c, uint8_t *out) {
    const uint8_t *Dx = DIST + (size_t)x * n;
    stamp++;
    int ns = 0;
    aff[c] = stamp; Slist[ns++] = c;
    for (int i = 0; i < ns; i++) {
        int s = Slist[i];
        for (int j = 0; j < dg[s]; j++) {
            int w = nb[s * DEG + j];
            if (Dx[w] != Dx[s] + 1 || evald[w] == stamp) continue;
            evald[w] = stamp;
            int all = 1;
            for (int k = 0; k < dg[w]; k++) {
                int q = nb[w * DEG + k];
                if (Dx[q] + 1 == Dx[w] && aff[q] != stamp) { all = 0; break; }
            }
            if (all) { aff[w] = stamp; Slist[ns++] = w; }
        }
    }
    for (int i = 0; i < ns; i++) nd[Slist[i]] = INFD;
    for (int i = 0; i < ns; i++) {
        int s = Slist[i];
        for (int j = 0; j < dg[s]; j++) {
            int y = nb[s * DEG + j];
            if (aff[y] == stamp) continue;
            if (s == c && y == p) continue;          /* the deleted edge */
            if (Dx[y] + 1 < nd[s]) nd[s] = Dx[y] + 1;
        }
    }
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < ns; i++) {
            int s = Slist[i];
            for (int j = 0; j < dg[s]; j++) {
                int y = nb[s * DEG + j];
                if (aff[y] != stamp) continue;
                if (nd[y] + 1 < nd[s]) { nd[s] = nd[y] + 1; changed = 1; }
            }
        }
    }
    int ok = 1;
    if (out) memcpy(out, Dx, n);
    for (int i = 0; i < ns; i++) {
        int s = Slist[i];
        if (nd[s] > DIAM) ok = 0;
        if (out) out[s] = (uint8_t)(nd[s] > 250 ? 250 : nd[s]);
    }
    return ok;
}
#define src_ok(x, p, c) src_core((x), (p), (c), NULL)

/* 1 if deleting edge uv keeps the diameter <= DIAM; *nX = number of sources that needed a repair */
static int edge_ok(int u, int v, int *nX) {
    int cnt = 0, ok = 1;
    for (int x = 0; x < n; x++) {
        if (PC[(size_t)v * n + x] == 1 && UP[(size_t)v * n + x] == u) {
            cnt++; if (!src_ok(x, u, v)) { ok = 0; break; }
        } else if (PC[(size_t)u * n + x] == 1 && UP[(size_t)u * n + x] == v) {
            cnt++; if (!src_ok(x, v, u)) { ok = 0; break; }
        }
    }
    if (nX) *nX = cnt;
    return ok;
}

/* bit-parallel all-pairs check on an arbitrary adjacency: connected and every distance <= DIAM */
static int apsp_ok(int N, const int *NB, const int *DG) {
    uint64_t *vis = malloc(8 * (size_t)N), *fr = malloc(8 * (size_t)N), *nx = malloc(8 * (size_t)N);
    int ok = 1;
    for (int s0 = 0; s0 < N && ok; s0 += 64) {
        int ns = N - s0 < 64 ? N - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, 8 * (size_t)N); memset(fr, 0, 8 * (size_t)N); memset(nx, 0, 8 * (size_t)N);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        int lev = 0;
        for (;;) {
            int any = 0;
            for (int x = 0; x < N; x++) {
                uint64_t acc = 0; const int *L = NB + (size_t)x * DEG;
                for (int j = 0; j < DG[x]; j++) acc |= fr[L[j]];
                acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1;
            }
            if (!any) break;
            lev++;
            if (lev > DIAM) { ok = 0; break; }
            for (int x = 0; x < N; x++) vis[x] |= nx[x];
            uint64_t *tmp = fr; fr = nx; nx = tmp;
        }
        if (!ok) break;
        for (int x = 0; x < N; x++) if (vis[x] != full) { ok = 0; break; }
    }
    free(vis); free(fr); free(nx);
    return ok;
}

static int brute_ok_without(int u, int v) {
    int *nb2 = malloc(sizeof(int) * (size_t)n * DEG), *dg2 = malloc(sizeof(int) * n);
    memcpy(nb2, nb, sizeof(int) * (size_t)n * DEG); memcpy(dg2, dg, sizeof(int) * n);
    for (int k = 0; k < dg2[u]; k++) if (nb2[u * DEG + k] == v) { nb2[u * DEG + k] = nb2[u * DEG + dg2[u] - 1]; dg2[u]--; break; }
    for (int k = 0; k < dg2[v]; k++) if (nb2[v * DEG + k] == u) { nb2[v * DEG + k] = nb2[v * DEG + dg2[v] - 1]; dg2[v]--; break; }
    int r = apsp_ok(n, nb2, dg2);
    free(nb2); free(dg2);
    return r;
}

/* greedy cover of the vertices of colour ucol by radius-3 balls of vertices of the other colour */
static int greedy_cover(int ucol, int *remaining_out) {
    int *unc = malloc(sizeof(int) * n); int rem = 0;
    for (int x = 0; x < n; x++) { unc[x] = (col[x] == ucol); rem += unc[x]; }
    int k = 0;
    while (rem > 0) {
        int best = -1, bestg = 0;
        for (int c = 0; c < n; c++) {
            if (col[c] == ucol) continue;
            const uint8_t *Dc = DIST + (size_t)c * n; int g = 0;
            for (int x = 0; x < n; x++) g += (unc[x] && Dc[x] <= 3);
            if (g > bestg) { bestg = g; best = c; }
        }
        if (best < 0) break;
        for (int x = 0; x < n; x++) if (unc[x] && DIST[(size_t)best * n + x] <= 3) { unc[x] = 0; rem--; }
        k++;
    }
    *remaining_out = rem;
    free(unc);
    return k;
}

static void write_graph(const char *fn, int N, const int *NB, const int *DG) {
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", N);
    for (int x = 0; x < N; x++) for (int j = 0; j < DG[x]; j++) { int y = NB[x * DEG + j]; if (x < y) fprintf(f, "%d %d\n", x, y); }
    fclose(f);
}

static int do_stats(void) {
    char *flag = malloc(m);
    long nonc = 0, sumX = 0; int maxX = 0;
    FILE *ff = fopen("edge_flags.txt", "w");
    for (int i = 0; i < m; i++) {
        int nX = 0; int g = edge_ok(eu[i], ev[i], &nX);
        flag[i] = (char)g; nonc += g; sumX += nX; if (nX > maxX) maxX = nX;
        fprintf(ff, "%d %d %d\n", eu[i], ev[i], g);
    }
    fclose(ff);
    printf("edges=%d noncritical=%ld critical=%ld avg_repaired_sources=%.1f max=%d\n",
           m, nonc, (long)m - nonc, (double)sumX / m, maxX);
    /* validation against brute-force APSP on G minus e */
    srand(12345);
    int K = 300, mism = 0, bf_nc = 0, bf_c = 0;
    for (int s = 0; s < K; s++) {
        int i = rand() % m;
        int nX; int g = edge_ok(eu[i], ev[i], &nX);
        int bf = brute_ok_without(eu[i], ev[i]);
        if (g != bf) mism++;
        if (bf) bf_nc++; else bf_c++;
    }
    printf("validation: sample=%d mismatches=%d brute_noncritical=%d brute_critical=%d\n", K, mism, bf_nc, bf_c);
    int rem; int kA = greedy_cover(0, &rem);
    printf("greedy radius-3 cover of A by B-balls: size=%d uncovered=%d\n", kA, rem);
    int kB = greedy_cover(1, &rem);
    printf("greedy radius-3 cover of B by A-balls: size=%d uncovered=%d\n", kB, rem);
    free(flag);
    return 0;
}

static int do_twin(int T, int seed) {
    srand(seed);
    int w0 = 0;                       /* vertex of colour 0 (side A) */
    int NB[DEG];
    for (int j = 0; j < DEG; j++) NB[j] = nb[w0 * DEG + j];
    static int opts[DEG][DEG]; int optsN[DEG];
    for (int j = 0; j < DEG; j++) {
        optsN[j] = 0;
        int b = NB[j];
        for (int k = 0; k < dg[b]; k++) {
            int a = nb[b * DEG + k];
            if (a == w0) continue;
            opts[j][optsN[j]++] = a;
        }
        
    }
    int N2 = n + 1;
    int *nb2 = malloc(sizeof(int) * (size_t)N2 * DEG), *dg2 = malloc(sizeof(int) * N2);
    int tried = 0, succ = 0;
    for (int t = 0; t < T; t++) {
        int chosen[DEG], okc = 1;
        for (int j = 0; j < DEG; j++) { if (optsN[j] == 0) { okc = 0; break; } chosen[j] = opts[j][rand() % optsN[j]]; }
        if (!okc) { printf("some neighbour has no removable partner; twin of w0 impossible\n"); break; }
        memcpy(nb2, nb, sizeof(int) * (size_t)n * DEG); memcpy(dg2, dg, sizeof(int) * n); dg2[n] = 0;
        for (int j = 0; j < DEG; j++) {
            int b = NB[j], a = chosen[j];
            for (int k = 0; k < DEG; k++) if (nb2[b * DEG + k] == a) { nb2[b * DEG + k] = n; break; }
            for (int k = 0; k < dg2[a]; k++) if (nb2[a * DEG + k] == b) { nb2[a * DEG + k] = nb2[a * DEG + dg2[a] - 1]; dg2[a]--; break; }
        }
        for (int j = 0; j < DEG; j++) nb2[n * DEG + j] = NB[j];
        dg2[n] = DEG;
        tried++;
        if (apsp_ok(N2, nb2, dg2)) {
            succ++;
            write_graph("aug_n7021.edges", N2, nb2, dg2);
            printf("SUCCESS on trial %d: wrote aug_n7021.edges (n=%d)\n", t, N2);
            break;
        }
    }
    printf("twin trials tried=%d success=%d\n", tried, succ);
    return 0;
}


static void bfs_skip(int x, int u, int v, int *bd, int *q) {
    for (int y = 0; y < n; y++) bd[y] = -1;
    int h = 0, t = 0; bd[x] = 0; q[t++] = x;
    while (h < t) {
        int y = q[h++];
        for (int j = 0; j < dg[y]; j++) {
            int w = nb[y * DEG + j];
            if ((y == u && w == v) || (y == v && w == u)) continue;
            if (bd[w] < 0) { bd[w] = bd[y] + 1; q[t++] = w; }
        }
    }
}
static int do_verify(int K, int seed) {
    srand(seed);
    uint8_t *row = malloc(n); int *bd = malloc(sizeof(int) * n); int *q = malloc(sizeof(int) * n);
    long mism_rows = 0, rows = 0, edges_nc = 0;
    for (int k = 0; k < K; k++) {
        int i = rand() % m; int u = eu[i], v = ev[i];
        int edge_mism = 0;
        for (int x = 0; x < n; x++) {
            int in1 = (PC[(size_t)v * n + x] == 1 && UP[(size_t)v * n + x] == u);
            int in2 = (PC[(size_t)u * n + x] == 1 && UP[(size_t)u * n + x] == v);
            if (in1) src_core(x, u, v, row);
            else if (in2) src_core(x, v, u, row);
            else memcpy(row, DIST + (size_t)x * n, n);
            bfs_skip(x, u, v, bd, q);
            for (int y = 0; y < n; y++) {
                int want = bd[y] < 0 ? 255 : bd[y];
                int got = row[y];
                if (want > 250) want = 250;
                if (got > 250) got = 250;
                if (want != got && !(want > DIAM && got > DIAM)) { edge_mism++; break; }
            }
            rows++;
            if (edge_mism) break;
        }
        if (edge_mism) mism_rows++;
        if (!edge_mism) edges_nc++;
    }
    printf("verify: edges=%d rowwise-mismatch-edges=%ld exact-distance-agreement-on-edges=%ld\n", K, mism_rows, edges_nc);
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 3) die("usage: augment EDGES stats | augment EDGES twin TRIALS SEED");
    read_graph(argv[1]);
    colour_and_check();
    build_dist();
    build_parents();
    aff = calloc(n, sizeof(int)); evald = calloc(n, sizeof(int)); nd = calloc(n, sizeof(int));
    Slist = malloc(sizeof(int) * n);
    if (strcmp(argv[2], "stats") == 0) return do_stats();
    if (strcmp(argv[2], "verify") == 0) return do_verify(argc > 3 ? atoi(argv[3]) : 10, argc > 4 ? atoi(argv[4]) : 1);
    if (strcmp(argv[2], "twin") == 0) return do_twin(argc > 3 ? atoi(argv[3]) : 100, argc > 4 ? atoi(argv[4]) : 1);
    die("unknown mode");
    return 1;
}
