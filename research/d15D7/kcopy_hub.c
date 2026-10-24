/* kcopy_hub.c: bipartite (q+1+k, 7) graphs from 2k+1 copies of the generalized hexagon H(q), plus hubs.
   cell-15-7 job, 2026-10-24. Reads a d7hex solution file (research/d15D7/d7hex.c, from the exp2-squad branch):
     "d7hex q N K n" / "freed p_1 .. p_K" / "hubedges m j k ..." / M[0..N-1] (a bijection points -> lines).

   Graph (r = 2k+1 copies, c in Z_r):
     (p,c) ~ (l,c) for p on l                              hexagon edges
     (p,c) ~ (M(p), c+j), j = 1..k, for p not freed        cross edges (all k bijections equal M)
     for each freed point p_a (l_a = M(p_a)) and j = 1..k:
       line-side hub  z_{a,j} ~ (p_a, c) for all c
       point-side hub w_{a,j} ~ (l_a, c) for all c
     hub graph: z_{a,1} ~ w_{b,1} for each listed pair (a, b)
   Max degree q+1+k (hubs: r + hub-graph degree). Vertices r*2N + 2kK.
   With no freed points this is the (2k+1)-copy table construction: diameter <= 7 for every bijection M.

   Why checking few sources suffices: in a bipartite graph, diameter <= 7 iff all same-side distances are <= 6.
   Point pairs (a,c),(b,c+j), j in 1..k: the route (a,c) -> (M(a),c+j) -> hexagon (<= 5) survives unless a is freed.
   Line pairs (l,c),(Z,c-j): (l,c) -> (M^-1(l),c-j) -> hexagon (<= 5) survives unless M^-1(l) is freed.
   Same-copy pairs: hexagon. So diameter <= 7 iff every freed source (p_a,0), (l_a,0) and every hub has
   eccentricity <= 7 (the graph is invariant under (v,c) -> (v,c+1), hubs fixed).

   Usage:
     kcopy_hub check HEXBIN SOL k          BFS from freed sources and hubs (exact, fast)
     kcopy_hub checkf HEXBIN SOL k         BFS from freed sources only, far-pair counts (for search checkpoints)
     kcopy_hub full  HEXBIN SOL k [T]      bit-parallel BFS from every copy-0 vertex and every hub (T threads)
     kcopy_hub edges HEXBIN SOL k OUT      write "n" then "u v" edges (for apsp.c / apsp_sym.c)              */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static int q, N, Q1, k, r, K, NV, HB;   /* HB = first hub id = r*2N */
static int32_t *LP, *PL;
static int *M, *Minv, *F, *isF;
static int HGm = 0, *HGj, *HGk;
static int **HGL, **HGP, *HGLn, *HGPn;

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + cnt[p]++] = l; }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "bad hexagon table\n"); exit(1); }
    free(cnt);
}

static void read_sol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int qq, nn, kk, nv; char w[16];
    if (fscanf(f, "d7hex %d %d %d %d %15s", &qq, &nn, &kk, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol header\n"); exit(1); }
    K = kk; F = malloc(sizeof(int) * (K + 1)); isF = calloc(N, sizeof(int));
    for (int a = 0; a < K; a++) { if (fscanf(f, "%d", &F[a]) != 1) exit(1); if (isF[F[a]]) { fprintf(stderr, "repeated freed point\n"); exit(1); } isF[F[a]] = a + 1; }
    long pos = ftell(f); char tok[32];
    if (fscanf(f, "%31s", tok) == 1 && !strcmp(tok, "hubedges")) {
        if (fscanf(f, "%d", &HGm) != 1) exit(1);
        HGj = malloc(sizeof(int) * (HGm + 1)); HGk = malloc(sizeof(int) * (HGm + 1));
        for (int e = 0; e < HGm; e++) if (fscanf(f, "%d %d", &HGj[e], &HGk[e]) != 2) exit(1);
    } else fseek(f, pos, SEEK_SET);
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N); for (int l = 0; l < N; l++) Minv[l] = -1;
    for (int p = 0; p < N; p++) {
        if (fscanf(f, "%d", &M[p]) != 1 || M[p] < 0 || M[p] >= N) { fprintf(stderr, "bad M\n"); exit(1); }
        if (Minv[M[p]] >= 0) { fprintf(stderr, "M not a bijection\n"); exit(1); }
        Minv[M[p]] = p;
    }
    fclose(f);
    HGL = malloc(sizeof(int *) * (K + 1)); HGP = malloc(sizeof(int *) * (K + 1));
    HGLn = calloc(K + 1, sizeof(int)); HGPn = calloc(K + 1, sizeof(int));
    for (int a = 0; a < K; a++) { HGL[a] = malloc(sizeof(int) * 64); HGP[a] = malloc(sizeof(int) * 64); }
    for (int e = 0; e < HGm; e++) {
        int j = HGj[e], b = HGk[e];
        if (j < 0 || j >= K || b < 0 || b >= K) { fprintf(stderr, "hub edge out of range\n"); exit(1); }
        for (int t = 0; t < HGLn[j]; t++) if (HGL[j][t] == b) { fprintf(stderr, "repeated hub edge\n"); exit(1); }
        if (HGLn[j] >= 64 || HGPn[b] >= 64) { fprintf(stderr, "hub degree too large\n"); exit(1); }
        HGL[j][HGLn[j]++] = b; HGP[b][HGPn[b]++] = j;
    }
    r = 2 * k + 1; HB = r * 2 * N; NV = HB + 2 * k * K;
}

/* hub ids: z_{a,j} = HB + a*k + (j-1); w_{a,j} = HB + k*K + a*k + (j-1) */
static inline int VP(int p, int c) { return c * 2 * N + p; }
static inline int VL(int l, int c) { return c * 2 * N + N + l; }
static int nbrs(int v, int *out) {
    int n = 0;
    if (v >= HB) {
        int h = v - HB;
        if (h < k * K) {                       /* line-side hub z_{a,j}: adjacent to points */
            int a = h / k, j = h % k + 1, p = F[a];
            for (int c = 0; c < r; c++) out[n++] = VP(p, c);
            if (j == 1) for (int t = 0; t < HGLn[a]; t++) out[n++] = HB + k * K + HGL[a][t] * k;
        } else {                               /* point-side hub w_{a,j}: adjacent to lines */
            h -= k * K; int a = h / k, j = h % k + 1, l = M[F[a]];
            for (int c = 0; c < r; c++) out[n++] = VL(l, c);
            if (j == 1) for (int t = 0; t < HGPn[a]; t++) out[n++] = HB + HGP[a][t] * k;
        }
        return n;
    }
    int c = v / (2 * N), x = v % (2 * N);
    if (x < N) {
        int p = x;
        for (int t = 0; t < Q1; t++) out[n++] = VL(PL[p * Q1 + t], c);
        if (isF[p]) { int a = isF[p] - 1; for (int j = 1; j <= k; j++) out[n++] = HB + a * k + (j - 1); }
        else for (int j = 1; j <= k; j++) out[n++] = VL(M[p], (c + j) % r);
    } else {
        int l = x - N;
        for (int t = 0; t < Q1; t++) out[n++] = VP(LP[l * Q1 + t], c);
        int p = Minv[l];
        if (isF[p]) { int a = isF[p] - 1; for (int j = 1; j <= k; j++) out[n++] = HB + k * K + a * k + (j - 1); }
        else for (int j = 1; j <= k; j++) out[n++] = VP(p, (c - j + r) % r);
    }
    return n;
}

static int bfs_ecc(int s, uint8_t *dist, int *que, long *bad) {
    memset(dist, 255, NV);
    int h = 0, t = 0, nb[128], e = 0; dist[s] = 0; que[t++] = s;
    while (h < t) {
        int v = que[h++]; int d = dist[v]; if (d > e) e = d;
        int c = nbrs(v, nb);
        for (int i = 0; i < c; i++) { int w = nb[i]; if (dist[w] == 255) { dist[w] = d + 1; que[t++] = w; } }
    }
    long b = NV - t; for (int i = 0; i < t; i++) if (dist[que[i]] > 7) b++;
    *bad = b;
    return t < NV ? 255 : e;
}

static void basic_stats(int *maxdeg, long *nedges) {
    int nb[128], md = 0; long m = 0;
    for (int v = 0; v < NV; v++) {
        int c = nbrs(v, nb); if (c > md) md = c; m += c;
        for (int i = 0; i < c; i++) {     /* symmetry and simplicity */
            int w = nb[i], nb2[128], c2 = nbrs(w, nb2), f = 0;
            for (int t = 0; t < c2; t++) if (nb2[t] == v) f++;
            if (f != 1) { fprintf(stderr, "adjacency not symmetric/simple at %d-%d\n", v, w); exit(1); }
            for (int t = i + 1; t < c; t++) if (nb[t] == w) { fprintf(stderr, "repeated edge at %d\n", v); exit(1); }
        }
    }
    *maxdeg = md; *nedges = m / 2;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: see header\n"); return 1; }
    load(argv[2]); k = atoi(argv[4]); read_sol(argv[3]);
    int Delta = q + 1 + k;
    if (!strcmp(argv[1], "fix")) {   /* kcopy_hub fix HEX SOL k OUT: repair far pairs by "safe" swaps of M (cell-15-7) */
        /* roleP[v]: flags b with d(v,p_b) in {2,4} (v's line is a side-A resource of b); roleL[N]: flags b with
           d(N,l_b) in {2,4} (N's preimage is a side-B resource of b). A swap that only touches elements with no role
           except the one it creates cannot break a type-2/4 route of any flag; BFS from all freed sources confirms. */
        uint64_t *roleP = calloc(N, 8), *roleL = calloc(N, 8); uint8_t *hd = malloc(2 * N);
        uint8_t **dpa = malloc(sizeof(void *) * K), **dla = malloc(sizeof(void *) * K);
        int *qq = malloc(sizeof(int) * 2 * N);
        for (int a = 0; a < K; a++) for (int s = 0; s < 2; s++) {
            uint8_t *d = malloc(2 * N); memset(d, 255, 2 * N); int h = 0, t = 0, st = s == 0 ? F[a] : N + M[F[a]]; d[st] = 0; qq[t++] = st;
            while (h < t) { int x = qq[h++];
                if (x < N) { for (int i = 0; i < Q1; i++) { int y = N + PL[x * Q1 + i]; if (d[y] == 255) { d[y] = d[x] + 1; qq[t++] = y; } } }
                else { int l = x - N; for (int i = 0; i < Q1; i++) { int y = LP[l * Q1 + i]; if (d[y] == 255) { d[y] = d[x] + 1; qq[t++] = y; } } } }
            if (s == 0) { dpa[a] = d; for (int v = 0; v < N; v++) if (d[v] == 2 || d[v] == 4) roleP[v] |= 1ULL << a; }
            else { dla[a] = d; for (int l = 0; l < N; l++) if (d[N + l] == 2 || d[N + l] == 4) roleL[l] |= 1ULL << a; }
        }
        uint8_t *dist = malloc(NV); int *que = malloc(sizeof(int) * NV);
        uint64_t rsd = 0x9E3779B97F4A7C15ULL;
        for (int round = 0; round < 200; round++) {
            long tot = 0; int fa = -1, fs = -1, ft = -1;
            for (int a = 0; a < K; a++) for (int s = 0; s < 2; s++) {
                int v = s == 0 ? VP(F[a], 0) : VL(M[F[a]], 0); long b; bfs_ecc(v, dist, que, &b); tot += b;
                if (b && fa < 0) { fa = a; fs = s; for (int x = 0; x < NV; x++) if (dist[x] > 7) { ft = x; break; } }
            }
            printf("round %d: far pairs %ld\n", round, tot); fflush(stdout);
            if (!tot) { FILE *f = fopen(argv[5], "w"); fprintf(f, "d7hex %d %d %d %d\nfreed", q, N, K, 6 * N + 2 * K);
                for (int a = 0; a < K; a++) fprintf(f, " %d", F[a]); fprintf(f, "\nhubedges %d", HGm);
                for (int e = 0; e < HGm; e++) fprintf(f, " %d %d", HGj[e], HGk[e]); fprintf(f, "\n");
                for (int p = 0; p < N; p++) fprintf(f, "%d%c", M[p], (p % 20 == 19 || p == N - 1) ? '\n' : ' ');
                fclose(f); printf("fixed: written %s\n", argv[5]); return 0; }
            if (ft < 0 || ft >= HB) { printf("far target is a hub or none: stop\n"); return 1; }
            int x = ft % (2 * N), done = 0; uint64_t me = 1ULL << fa;
            if (fs == 0 && x < N) {          /* point x opposite p_a: give a line N through x to some u at distance 4 from p_a */
                for (int i = 0; i < Q1 && !done; i++) { int Nl = PL[x * Q1 + i]; if (roleL[Nl]) continue; int w = Minv[Nl]; if (isF[w] || roleP[w]) continue;
                    for (int tr = 0; tr < 400000 && !done; tr++) { rsd ^= rsd << 13; rsd ^= rsd >> 7; rsd ^= rsd << 17; int u = rsd % N;
                        if (dpa[fa][u] != 4 || isF[u] || (roleP[u] & ~me)) continue; int O = M[u]; if (roleL[O]) continue;
                        M[u] = Nl; Minv[Nl] = u; M[w] = O; Minv[O] = w; done = 1; printf("  swap: point %d takes line %d (through far point %d), point %d takes line %d\n", u, Nl, x, w, O); } }
            } else if (fs == 1 && x >= N) {  /* line t opposite l_a: give a line U at distance 4 from l_a to some point y on t */
                int t = x - N;
                for (int i = 0; i < Q1 && !done; i++) { int y = LP[t * Q1 + i]; if (isF[y] || roleP[y]) continue; int O = M[y]; if (roleL[O]) continue;
                    for (int tr = 0; tr < 400000 && !done; tr++) { rsd ^= rsd << 13; rsd ^= rsd >> 7; rsd ^= rsd << 17; int U = rsd % N;
                        if (dla[fa][N + U] != 4 || (roleL[U] & ~me)) continue; int w = Minv[U]; if (isF[w] || roleP[w] || w == y) continue;
                        M[y] = U; Minv[U] = y; M[w] = O; Minv[O] = w; done = 1; printf("  swap: point %d (on far line %d) takes line %d, point %d takes line %d\n", y, t, U, w, O); } }
            }
            if (!done) { printf("no safe swap for flag %d side %d target %d: stop\n", fa, fs, ft); return 1; }
        }
        return 1;
    }
    if (!strcmp(argv[1], "checkf")) {   /* freed sources only (hubs reach everything whatever M is), with far-pair counts */
        uint8_t *dist = malloc(NV); int *que = malloc(sizeof(int) * NV); long tot = 0; int badsrc = 0;
        for (int a = 0; a < K; a++) for (int s = 0; s < 2; s++) {
            int v = s == 0 ? VP(F[a], 0) : VL(M[F[a]], 0); long b; bfs_ecc(v, dist, que, &b);
            if (b) { badsrc++; tot += b; printf("flag %d %s: %ld far\n", a, s ? "line" : "point", b); }
        }
        printf("checkf q=%d k=%d K=%d n=%d: bad freed sources %d, far pairs %ld -> %s\n", q, k, K, NV, badsrc, tot, tot ? "FAIL" : "OK");
        return 0;
    }
    if (!strcmp(argv[1], "check")) {
        int md; long m; basic_stats(&md, &m);
        printf("q=%d k=%d copies=%d K=%d hubedges=%d n=%d edges=%ld maxdeg=%d (Delta %d)\n", q, k, r, K, HGm, NV, m, md, Delta);
        uint8_t *dist = malloc(NV); int *que = malloc(sizeof(int) * NV);
        int worst = 0, badsrc = 0; long badpairs = 0;
        int nsrc = 0;
        for (int a = 0; a < K; a++) for (int s = 0; s < 2; s++) {
            int v = s == 0 ? VP(F[a], 0) : VL(M[F[a]], 0); long b; int e = bfs_ecc(v, dist, que, &b);
            if (e > worst) worst = e; if (b) { badsrc++; badpairs += b; } nsrc++;
        }
        for (int v = HB; v < NV; v++) { long b; int e = bfs_ecc(v, dist, que, &b); if (e > worst) worst = e; if (b) { badsrc++; badpairs += b; } nsrc++; }
        printf("freed sources and hubs: %d sources, max eccentricity %d, bad sources %d, far pairs %ld -> %s\n",
               nsrc, worst, badsrc, badpairs, (badsrc == 0 && md <= Delta) ? "OK" : "FAIL");
        return 0;
    }
    if (!strcmp(argv[1], "edges")) {
        FILE *f = fopen(argv[5], "w"); fprintf(f, "%d\n", NV); int nb[128]; long m = 0;
        for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); for (int i = 0; i < c; i++) if (nb[i] > v) { fprintf(f, "%d %d\n", v, nb[i]); m++; } }
        fclose(f); fprintf(stderr, "wrote %s: n=%d edges=%ld\n", argv[5], NV, m);
        return 0;
    }
    if (!strcmp(argv[1], "full")) {
        int T = argc > 5 ? atoi(argv[5]) : 1;
        int md; long m; basic_stats(&md, &m);
        printf("q=%d k=%d copies=%d K=%d n=%d edges=%ld maxdeg=%d (Delta %d)\n", q, k, r, K, NV, m, md, Delta); fflush(stdout);
        /* CSR adjacency */
        long *st = malloc(sizeof(long) * (NV + 1)); int nb[128]; st[0] = 0;
        for (int v = 0; v < NV; v++) st[v + 1] = st[v] + nbrs(v, nb);
        int *adj = malloc(sizeof(int) * st[NV]);
        for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); memcpy(adj + st[v], nb, sizeof(int) * c); }
        int nsrc = 2 * N + 2 * k * K; int *src = malloc(sizeof(int) * nsrc);
        for (int v = 0; v < 2 * N; v++) src[v] = v;
        for (int h = 0; h < 2 * k * K; h++) src[2 * N + h] = HB + h;
        int nbatch = (nsrc + 63) / 64; long done = 0; int gdiam = 0, gbad = 0; time_t t0 = time(NULL);
#ifdef _OPENMP
        omp_set_num_threads(T);
#endif
        #pragma omp parallel
        {
            uint64_t *vis = malloc(8 * (size_t)NV), *fr = malloc(8 * (size_t)NV), *nx = malloc(8 * (size_t)NV);
            #pragma omp for schedule(dynamic, 4)
            for (int b = 0; b < nbatch; b++) {
                memset(vis, 0, 8 * (size_t)NV); memset(fr, 0, 8 * (size_t)NV);
                int s0 = b * 64, ns = nsrc - s0 < 64 ? nsrc - s0 : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
                for (int i = 0; i < ns; i++) { vis[src[s0 + i]] |= 1ULL << i; fr[src[s0 + i]] |= 1ULL << i; }
                int lev = 0;
                for (;;) {
                    int any = 0;
                    for (int x = 0; x < NV; x++) {
                        uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]];
                        acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1;
                    }
                    if (!any) break;
                    lev++; for (int x = 0; x < NV; x++) vis[x] |= nx[x];
                    uint64_t *tp = fr; fr = nx; nx = tp;
                    if (lev > 8) break;
                }
                int bad = 0; for (int x = 0; x < NV; x++) if (vis[x] != full) { bad = 1; break; }
                #pragma omp critical
                {
                    if (lev > gdiam) gdiam = lev; if (bad) gbad++;
                    done++;
                    if (done % 200 == 0) { fprintf(stderr, "batch %ld/%d diam so far %d bad %d (%lds)\n", done, nbatch, gdiam, gbad, (long)(time(NULL) - t0)); }
                }
            }
            free(vis); free(fr); free(nx);
        }
        printf("full symmetric check: %d sources (copy 0 and hubs), max eccentricity %d, bad batches %d -> %s\n", nsrc, gdiam, gbad,
               (gbad == 0 && gdiam <= 7 && md <= Delta) ? "VALID" : "INVALID");
        return 0;
    }
    return 1;
}
