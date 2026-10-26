/* omegaref.c (referee omega-dq): Gomez's Omega H_q (thesis UPC 1986, sec. 2.9.3, Figs 2.21a/b), built from scratch
   in memory from the incidence graph of H(q) (hexgen output), then BFS from chosen sources.
   Notation: n1 = number of points = number of lines; base vertex v in [0, 2 n1): points 0..n1-1, lines n1..2n1-1.
     copies c = 5B + i (block B = 0..alpha-1, i in Z5), copy vertex id = c*2n1 + v;
     copies of K1: K(t,k,bar) (bar = 0 for the sets k, 1 for the sets kbar), id = 5*alpha*2n1 + (5*bar + k)*n1 + t.
   Fig 2.21a (type a): K(t,k,0) on the INNER dot of copies k-1, k+1 (star); K(t,k,1) on the OUTER dot of copies k+2, k+3.
   Fig 2.21b (type b): K(t,k,0) on the OUTER dot of copies k+3, k+4 (circle); K(t,k,1) on the INNER dot of copies k-1, k+1.
   The dot of label t is point t or line sigma(t):
     reading 2: K(t,k,0) always on point t, K(t,k,1) always on line sigma(t);
     reading 1: inner dot = line sigma(t), outer dot = point t (in every copy).
   usage: omegaref hex.txt q types(e.g. ababa) reading(1|2) sigma(id|rand:SEED) mode
     mode "src ID [ID ...]"   BFS from these vertex ids (-1 = K(0,0,0), -2 = K(0,0,1))
     mode "reps"              BFS from K(0,0,0), K(0,0,1) and point 0 / line 0 of the first copy of each block type
     mode "sample N SEED"     BFS from N random vertices
     mode "kall"              BFS from every K(t,0,0), t = 0..n1-1 (eccentricity profile only)
     mode "exact [threads]"   exact diameter: checks the rotation and block swaps are automorphisms, then
                              64-source BFS from one vertex of every orbit of the group they generate */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>

static int n1, alpha, C, N, q;
static long K0;
static int *hoff, *hadj;          /* base graph CSR */
static int *off, *adj;            /* Omega graph CSR */
static char types[64]; static int reading;
static int *sig;

static unsigned long long rng = 88172645463325252ULL;
static unsigned long long xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void decode(int id, char *buf) {
    if (id < K0) { int c = id / (2 * n1), v = id % (2 * n1);
        sprintf(buf, "copy %d (block %d type %c, i=%d) %s %d", c, c / 5, types[c / 5], c % 5, v < n1 ? "point" : "line", v < n1 ? v : v - n1);
    } else { int r = id - K0, t = r % n1, kb = r / n1;
        sprintf(buf, "K(t=%d, %s%d)", t, kb >= 5 ? "kbar=" : "k=", kb % 5); }
}

static void hbfs(int s, int *d) {           /* BFS in the base hexagon incidence graph */
    int *qu = malloc(sizeof(int) * 2 * n1), h = 0, t = 0;
    for (int i = 0; i < 2 * n1; i++) d[i] = -1;
    d[s] = 0; qu[t++] = s;
    while (h < t) { int x = qu[h++]; for (int e = hoff[x]; e < hoff[x + 1]; e++) if (d[hadj[e]] < 0) { d[hadj[e]] = d[x] + 1; qu[t++] = hadj[e]; } }
    free(qu);
}

static int *dist, *qu;
static int bfs(int s) {
    for (int i = 0; i < N; i++) dist[i] = -1;
    int h = 0, t = 0; dist[s] = 0; qu[t++] = s;
    while (h < t) { int x = qu[h++]; for (int e = off[x]; e < off[x + 1]; e++) if (dist[adj[e]] < 0) { dist[adj[e]] = dist[x] + 1; qu[t++] = adj[e]; } }
    if (t != N) return -1;
    return dist[qu[N - 1]];
}

/* full report for one source */
static void report(int s) {
    char b1[200], b2[200];
    int ecc = bfs(s);
    long cnt[64] = {0}; for (int i = 0; i < N; i++) if (dist[i] >= 0) cnt[dist[i]]++;
    decode(s, b1);
    printf("source %d = %s: eccentricity %d; counts by distance:", s, b1, ecc);
    for (int d = 0; d <= ecc; d++) printf(" %ld", cnt[d]);
    printf("\n");
    if (ecc < 0) return;
    int w = -1; for (int i = 0; i < N; i++) if (dist[i] == ecc) { w = i; break; }
    decode(w, b2);
    printf("  witness: d(%d, %d) = %d, target %s\n", s, w, ecc, b2);
    if (s >= K0) {                          /* a copy of K1: which copies it meets, and where the far vertices are */
        int t = (s - K0) % n1;
        int *dp = malloc(sizeof(int) * 2 * n1), *dl = malloc(sizeof(int) * 2 * n1);
        hbfs(t, dp); hbfs(n1 + sig[t], dl);
        char *meets = calloc(C, 1);
        for (int e = off[s]; e < off[s + 1]; e++) meets[adj[e] / (2 * n1)] = 1;
        int nm = 0; for (int c = 0; c < C; c++) nm += meets[c];
        if (w < K0) { int v = w % (2 * n1);
            printf("  witness base vertex %d: d_H(point t, it) = %d, d_H(line sigma(t), it) = %d; source meets its copy: %s\n",
                   v, dp[v], dl[v], meets[w / (2 * n1)] ? "yes" : "no"); }
        long far = 0, farmissed = 0, farpt_opp = 0, farline_opp = 0, farother = 0;
        for (int i = 0; i < N; i++) if (dist[i] >= 9) {
            far++;
            if (i >= K0) { farother++; continue; }
            int c = i / (2 * n1), v = i % (2 * n1);
            if (!meets[c]) farmissed++;
            if (v < n1 && dp[v] == 6) farpt_opp++; else if (v >= n1 && dl[v] == 6) farline_opp++; else farother++;
        }
        printf("  source meets %d of %d copies; %ld vertices at distance >= 9: %ld in copies it misses; "
               "%ld points opposite point t, %ld lines opposite line sigma(t), %ld other\n",
               nm, C, far, farmissed, farpt_opp, farline_opp, farother);
        /* Theorem 2 count: in each missed copy, vertices at odd distance that are opposite their label's partner
           (a line opposite line sigma(t), a point opposite point t), and how many of them are within distance 7 */
        long worst = 0;
        for (int c = 0; c < C; c++) if (!meets[c]) {
            long near = 0, opp = 0;
            for (int v = 0; v < 2 * n1; v++) { int i = c * 2 * n1 + v; if (dist[i] % 2 == 0) continue;
                int o = v < n1 ? dp[v] == 6 : dl[v] == 6; if (!o) continue; opp++; if (dist[i] <= 7) near++; }
            if (near > worst) worst = near;
            if (opp == 0) printf("  (no odd-distance opposite vertices in copy %d?)\n", c);
        }
        printf("  Theorem 2 check: in a missed copy, at most %ld opposite vertices of the odd class are within distance 7\n", worst);
        free(dp); free(dl); free(meets);
    }
}

/* mode "exact": the exact diameter without any assumption on Aut(H(q)).
   (1) checks edge by edge that the rotation (copy 5B+i -> 5B+i+1, K(t,k,bar) -> K(t,k+1,bar)) and the swaps of the first
       block of each type with every other block of that type are automorphisms;
   (2) every vertex is then in the orbit of a K(t,0,bar) or of a vertex of the first copy of the first block of its type,
       so the diameter is the largest eccentricity over those 2 n1 + 2 n1 * (number of types) sources, found by 64-source
       bit-parallel BFS. */
static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }
static int has_edge(int u, int w) {
    int lo = off[u], hi = off[u + 1] - 1;
    while (lo <= hi) { int m = (lo + hi) / 2; if (adj[m] == w) return 1; if (adj[m] < w) lo = m + 1; else hi = m - 1; }
    return 0;
}
static int check_map(const int *img, const char *name) {
    char *seen = calloc(N, 1); long bad = 0;
    for (int i = 0; i < N; i++) { if (img[i] < 0 || img[i] >= N || seen[img[i]]) { bad++; continue; } seen[img[i]] = 1; }
    for (int i = 0; i < N && !bad; i++) for (int e = off[i]; e < off[i + 1]; e++) if (!has_edge(img[i], img[adj[e]])) bad++;
    printf("  %s: %s\n", name, bad ? "NOT an automorphism" : "bijection, maps every edge to an edge");
    free(seen); return bad == 0;
}
static int *srcs, nsrc, next_b; static int *eccs; static long unreached_all;
static pthread_mutex_t mtx = PTHREAD_MUTEX_INITIALIZER;
static void *exact_worker(void *arg) {
    (void)arg;
    uint64_t *vis = malloc(8L * N), *fr = malloc(8L * N), *nf = malloc(8L * N);
    for (;;) {
        pthread_mutex_lock(&mtx); int b = next_b++; pthread_mutex_unlock(&mtx);
        if (64L * b >= nsrc) break;
        int s0 = 64 * b, ns = nsrc - s0 < 64 ? nsrc - s0 : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, 8L * N); memset(fr, 0, 8L * N);
        for (int i = 0; i < ns; i++) { vis[srcs[s0 + i]] |= 1ULL << i; fr[srcs[s0 + i]] |= 1ULL << i; }
        int ecc[64] = {0}, lev = 0;
        for (;;) {
            uint64_t alive = 0;
            for (int v = 0; v < N; v++) {
                uint64_t a = 0;
                for (int e = off[v]; e < off[v + 1]; e++) a |= fr[adj[e]];
                a &= ~vis[v]; nf[v] = a; alive |= a;
            }
            if (!alive) break;
            lev++;
            for (int i = 0; i < ns; i++) if (alive >> i & 1) ecc[i] = lev;
            for (int v = 0; v < N; v++) vis[v] |= nf[v];
            uint64_t *t = fr; fr = nf; nf = t;
        }
        long un = 0; for (int v = 0; v < N; v++) un += __builtin_popcountll(full & ~vis[v]);
        pthread_mutex_lock(&mtx);
        for (int i = 0; i < ns; i++) eccs[s0 + i] = ecc[i];
        unreached_all += un;
        pthread_mutex_unlock(&mtx);
    }
    free(vis); free(fr); free(nf); return NULL;
}
static void exact(int nth) {
    for (int i = 0; i < N; i++) qsort(adj + off[i], off[i + 1] - off[i], sizeof(int), cmpint);
    int *img = malloc(sizeof(int) * N), ok = 1;
    for (int i = 0; i < N; i++) {
        if (i < K0) { int c = i / (2 * n1), v = i % (2 * n1); img[i] = (5 * (c / 5) + (c % 5 + 1) % 5) * 2 * n1 + v; }
        else { int r = i - K0, t = r % n1, kb = r / n1, bar = kb / 5, k = kb % 5; img[i] = K0 + (5 * bar + (k + 1) % 5) * n1 + t; }
    }
    ok &= check_map(img, "rotation");
    int first[2] = {-1, -1};
    for (int B = 0; B < alpha; B++) { int ty = types[B] == 'b';
        if (first[ty] < 0) { first[ty] = B; continue; }
        for (int i = 0; i < N; i++) {
            img[i] = i;
            if (i < K0) { int c = i / (2 * n1), v = i % (2 * n1), cb = c / 5;
                if (cb == B) img[i] = (5 * first[ty] + c % 5) * 2 * n1 + v;
                else if (cb == first[ty]) img[i] = (5 * B + c % 5) * 2 * n1 + v; }
        }
        char nm[64]; sprintf(nm, "swap of blocks %d and %d", first[ty], B);
        ok &= check_map(img, nm);
    }
    if (!ok) { printf("  symmetry check failed; no exact result\n"); return; }
    nsrc = 0; srcs = malloc(sizeof(int) * (2 * n1 + 4 * n1));
    for (int bar = 0; bar < 2; bar++) for (int t = 0; t < n1; t++) srcs[nsrc++] = K0 + 5 * bar * n1 + t;
    for (int ty = 0; ty < 2; ty++) if (first[ty] >= 0) for (int v = 0; v < 2 * n1; v++) srcs[nsrc++] = 5 * first[ty] * 2 * n1 + v;
    eccs = malloc(sizeof(int) * nsrc);
    pthread_t th[64]; next_b = 0; unreached_all = 0;
    for (int i = 0; i < nth; i++) pthread_create(&th[i], NULL, exact_worker, NULL);
    for (int i = 0; i < nth; i++) pthread_join(th[i], NULL);
    long hk[64] = {0}, hc[64] = {0}; int mx = 0, arg = -1;
    for (int i = 0; i < nsrc; i++) { if (srcs[i] >= K0) hk[eccs[i]]++; else hc[eccs[i]]++; if (eccs[i] > mx) { mx = eccs[i]; arg = srcs[i]; } }
    printf("  %d sources (all K(t,0,bar); all vertices of the first copy of each block type): unreached pairs %ld\n", nsrc, unreached_all);
    printf("  eccentricity of K1-vertex sources:"); for (int d = 0; d < 64; d++) if (hk[d]) printf(" %d:%ld", d, hk[d]);
    printf("\n  eccentricity of copy-vertex sources:"); for (int d = 0; d < 64; d++) if (hc[d]) printf(" %d:%ld", d, hc[d]);
    char b1[200]; decode(arg, b1);
    printf("\n  DIAMETER %d (every vertex is in the orbit of a source; largest eccentricity at %d = %s)\n",
           unreached_all ? -1 : mx, arg, b1);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: see header\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); int nb; if (!f || fscanf(f, "%d", &nb) != 1) return 1;
    q = atoi(argv[2]); strcpy(types, argv[3]); reading = atoi(argv[4]);
    n1 = nb / 2; alpha = strlen(types); C = 5 * alpha;
    if (q + 3 != 2 * alpha && q + 3 != 2 * alpha + 1) { fprintf(stderr, "need q+3 = 2 alpha + beta\n"); return 1; }
    /* base graph */
    long hm = (long)n1 * (q + 1); int *eu = malloc(sizeof(int) * hm), *ev = malloc(sizeof(int) * hm); long m = 0;
    while (m < hm && fscanf(f, "%d %d", &eu[m], &ev[m]) == 2) m++;
    fclose(f); if (m != hm) { fprintf(stderr, "edge count %ld != %ld\n", m, hm); return 1; }
    hoff = calloc(2 * n1 + 1, sizeof(int)); hadj = malloc(sizeof(int) * 2 * hm);
    for (long e = 0; e < hm; e++) { hoff[eu[e] + 1]++; hoff[ev[e] + 1]++; }
    for (int i = 0; i < 2 * n1; i++) hoff[i + 1] += hoff[i];
    { int *p = malloc(sizeof(int) * 2 * n1); memcpy(p, hoff, sizeof(int) * 2 * n1);
      for (long e = 0; e < hm; e++) { hadj[p[eu[e]]++] = ev[e]; hadj[p[ev[e]]++] = eu[e]; } free(p); }
    /* sigma */
    sig = malloc(sizeof(int) * n1); for (int t = 0; t < n1; t++) sig[t] = t;
    if (!strncmp(argv[5], "rand:", 5)) { rng += strtoull(argv[5] + 5, 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
        for (int t = n1 - 1; t > 0; t--) { int r = xr() % (t + 1); int z = sig[t]; sig[t] = sig[r]; sig[r] = z; } }
    /* Omega edges */
    K0 = (long)C * 2 * n1; N = K0 + 10L * n1;
    long M = (long)C * hm + 10L * n1 * 2 * alpha, me = 0;
    int *U = malloc(sizeof(int) * M), *V = malloc(sizeof(int) * M);
    for (int c = 0; c < C; c++) for (long e = 0; e < hm; e++) { U[me] = c * 2 * n1 + eu[e]; V[me] = c * 2 * n1 + ev[e]; me++; }
    for (int B = 0; B < alpha; B++) for (int t = 0; t < n1; t++) for (int k = 0; k < 5; k++) for (int bar = 0; bar < 2; bar++) {
        int i1, i2, inner;
        if (types[B] == 'a') { if (!bar) { i1 = k + 4; i2 = k + 1; inner = 1; } else { i1 = k + 2; i2 = k + 3; inner = 0; } }
        else                 { if (!bar) { i1 = k + 3; i2 = k + 4; inner = 0; } else { i1 = k + 4; i2 = k + 1; inner = 1; } }
        int useline = reading == 2 ? bar : inner;
        int v = useline ? n1 + sig[t] : t;
        int h = K0 + (5 * bar + k) * n1 + t;
        int cs[2] = { 5 * B + i1 % 5, 5 * B + i2 % 5 };
        for (int j = 0; j < 2; j++) { U[me] = h; V[me] = cs[j] * 2 * n1 + v; me++; }
    }
    if (me != M) { fprintf(stderr, "edge count\n"); return 1; }
    off = calloc(N + 1, sizeof(int)); adj = malloc(sizeof(int) * 2 * M);
    for (long e = 0; e < M; e++) { off[U[e] + 1]++; off[V[e] + 1]++; }
    for (int i = 0; i < N; i++) off[i + 1] += off[i];
    { int *p = malloc(sizeof(int) * N); memcpy(p, off, sizeof(int) * N);
      for (long e = 0; e < M; e++) { adj[p[U[e]]++] = V[e]; adj[p[V[e]]++] = U[e]; } free(p); }
    /* structural checks: degrees, simple, bipartite, connected */
    int dmin = 1 << 30, dmax = 0, kmin = 1 << 30, kmax = 0; long multi = 0;
    int *mk = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) mk[i] = -1;
    for (int i = 0; i < N; i++) { int d = off[i + 1] - off[i];
        if (i < K0) { if (d < dmin) dmin = d; if (d > dmax) dmax = d; } else { if (d < kmin) kmin = d; if (d > kmax) kmax = d; }
        for (int e = off[i]; e < off[i + 1]; e++) { if (mk[adj[e]] == i || adj[e] == i) multi++; mk[adj[e]] = i; } }
    dist = malloc(sizeof(int) * N); qu = malloc(sizeof(int) * N);
    int ecc0 = bfs(0), bip = 1;
    for (int i = 0; i < N && bip; i++) for (int e = off[i]; e < off[i + 1]; e++) if ((dist[i] ^ dist[adj[e]]) % 2 == 0) { bip = 0; break; }
    printf("Omega H_%d reading %d types %s sigma %s: vertices %d (copies %d x %d + K1-vertices %d), edges %ld\n",
           q, reading, types, argv[5], N, C, 2 * n1, 10 * n1, M);
    printf("  copy-vertex degree %d..%d, K1-vertex degree %d..%d, loops/multi-edges %ld, connected %s, bipartite %s\n",
           dmin, dmax, kmin, kmax, multi, ecc0 >= 0 ? "yes" : "no", bip ? "yes" : "no");
    fflush(stdout);
    const char *mode = argv[6];
    if (!strcmp(mode, "src")) {
        for (int a = 7; a < argc; a++) { int s = atoi(argv[a]); if (s == -1) s = K0; if (s == -2) s = K0 + 5 * n1; report(s); fflush(stdout); }
    } else if (!strcmp(mode, "reps")) {
        report(K0); report(K0 + 5 * n1);
        char seen[2] = {0, 0};
        for (int B = 0; B < alpha; B++) { int ty = types[B] == 'b'; if (seen[ty]) continue; seen[ty] = 1;
            report(5 * B * 2 * n1); report(5 * B * 2 * n1 + n1); }
    } else if (!strcmp(mode, "sample")) {
        int ns = atoi(argv[7]); rng ^= strtoull(argv[8], 0, 10) * 0xD1B54A32D192ED03ULL; for (int i = 0; i < 10; i++) xr();
        int mx = 0, mn = 1 << 30; long hist[64] = {0}, histK[64] = {0};
        for (int j = 0; j < ns; j++) { int s = xr() % N; int e = bfs(s); if (e < 0) { printf("disconnected\n"); return 1; }
            if (e > mx) mx = e;
            if (e < mn) mn = e;
            if (s >= K0) histK[e]++; else hist[e]++; }
        printf("  %d random sources: eccentricity min %d max %d; copy vertices by ecc:", ns, mn, mx);
        for (int d = 0; d <= mx; d++) if (hist[d]) printf(" %d:%ld", d, hist[d]);
        printf("; K1-vertices by ecc:"); for (int d = 0; d <= mx; d++) if (histK[d]) printf(" %d:%ld", d, histK[d]);
        printf("\n");
    } else if (!strcmp(mode, "kall")) {
        long hist[64] = {0};
        for (int t = 0; t < n1; t++) { int e = bfs(K0 + t); hist[e < 0 ? 0 : e]++; }
        printf("  all %d sources K(t,0,0): eccentricity histogram:", n1);
        for (int d = 0; d < 64; d++) if (hist[d]) printf(" %d:%ld", d, hist[d]);
        printf("\n");
    } else if (!strcmp(mode, "exact")) {
        exact(argc > 7 ? atoi(argv[7]) : 4);
    }
    return 0;
}
