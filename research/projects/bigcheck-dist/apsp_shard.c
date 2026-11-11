/* apsp_shard.c: the all-pairs check of apsp_mt.c and apsp_orb.c, split into shards that run in separate sessions.
   Sources are numbered 0..nsrc-1 and grouped in batches of 64: batch b holds sources s = 64b .. 64b+63. Shard I of K
   runs the batches b with b % K == I and prints one report: a line per batch with its largest eccentricity.
   Layout "full": the sources are all n vertices. Layout "L,B" (level cover, as in apsp_orb.c): vertices [0, LB) are L
   levels of B vertices, [LB, n) are hubs; the level shift v -> (v + B) mod LB is checked edge by edge to be an
   automorphism, and the sources are [0, B) plus the hubs. Every orbit of the shift meets [0, B) and eccentricity is
   constant on orbits, so the largest eccentricity over those sources is the diameter.
   Each shard checks the structure itself (simple, degrees, bipartite, connected) and reports it. merge reads the edge
   file (for n, m and an order-independent fingerprint) and all K reports, and accepts only a complete, consistent set:
   every shard once, the same graph, layout, parameters and structure, exactly the batches its shard owns, each with a
   finished BFS. A merge certifies the reports; it does not redo the arithmetic. Reports do not depend on the thread
   count, so any shard can be rerun and diffed byte for byte.
   Usage: apsp_shard shard EDGES d D K I T full|L,B > report_I.txt
          apsp_shard merge EDGES d D K full|L,B report_0.txt ... report_{K-1}.txt
   Exit: shard 0 on a valid report, 1 if the graph fails a check; merge 0 if RESULT VALID, 1 if RESULT INVALID or a
   report is rejected, 2 on usage or file errors.
   Build: cc -O2 -pthread -o apsp_shard apsp_shard.c */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static long n, m, *st, *adj, LB, B, nbat, nsrc, K, I, next_b;
static int *ecc, bad = 0;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;

static uint64_t mix(uint64_t x) { /* splitmix64 finaliser */
    x += 0x9E3779B97F4A7C15ULL; x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL; x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL;
    return x ^ (x >> 31);
}
static long source(long i) { return i < B ? i : LB + (i - B); } /* B = LB = 0 for layout full */
static int cmpl(const void *a, const void *b) { long x = *(const long *)a, y = *(const long *)b; return x < y ? -1 : x > y; }
static int has_edge(long u, long v) {
    long lo = st[u], hi = st[u + 1] - 1;
    while (lo <= hi) { long mid = (lo + hi) / 2; if (adj[mid] == v) return 1; if (adj[mid] < v) lo = mid + 1; else hi = mid - 1; }
    return 0;
}
static void *work(void *unused) {
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    for (;;) {
        pthread_mutex_lock(&mu); long b = next_b; next_b += K; int stop = bad; pthread_mutex_unlock(&mu);
        if (b >= nbat || stop) break;
        long s0 = b * 64;
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        int ns = (nsrc - s0 < 64) ? (int)(nsrc - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { long x = source(s0 + k); vis[x] |= 1ULL << k; fr[x] |= 1ULL << k; }
        int lev = 0;
        for (;;) { int any = 0;
            for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            if (!any) break;
            lev++; for (long x = 0; x < n; x++) vis[x] |= nx[x];
            uint64_t *tmp = fr; fr = nx; nx = tmp;
        }
        int unreached = 0;
        for (long x = 0; x < n; x++) if (vis[x] != full) { unreached = 1; break; }
        if (unreached) { pthread_mutex_lock(&mu); bad = 1; pthread_mutex_unlock(&mu); break; }
        ecc[b] = lev; /* each batch is taken by exactly one thread */
    }
    free(vis); free(fr); free(nx); return NULL;
}
/* Reads n, m, the edge arrays and the fingerprint: sum over edges of mix(min * n + max), order independent. */
static void read_graph(const char *file, long **U, long **W, uint64_t *fp) {
    FILE *f = fopen(file, "r"); long cap = 1 << 20, a, b; *U = malloc(cap * 8); *W = malloc(cap * 8); m = 0;
    if (!f || fscanf(f, "%ld", &n) != 1) { printf("REJECT cannot read %s\n", file); exit(2); }
    if (n < 1 || n >= (1L << 32)) { printf("REJECT n out of range\n"); exit(2); }
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; *U = realloc(*U, cap * 8); *W = realloc(*W, cap * 8); }
        (*U)[m] = a; (*W)[m] = b; m++;
    }
    fclose(f);
    *fp = 0;
    for (long i = 0; i < m; i++) {
        long lo = (*U)[i] < (*W)[i] ? (*U)[i] : (*W)[i], hi = (*U)[i] < (*W)[i] ? (*W)[i] : (*U)[i];
        if (lo < 0 || hi >= n || lo == hi) continue; /* shards reject these; merge only needs the same sum */
        *fp += mix((uint64_t)lo * (uint64_t)n + (uint64_t)hi);
    }
}
static int parse_layout(const char *s, int *full) {
    if (!strcmp(s, "full")) { *full = 1; LB = 0; B = 0; return 1; }
    long L, Bb; if (sscanf(s, "%ld,%ld", &L, &Bb) != 2 || L < 1 || Bb < 1) return 0;
    *full = 0; B = Bb; LB = L * Bb; return 1;
}
static int run_shard(int argc, char **argv) {
    if (argc != 9) { printf("usage: apsp_shard shard EDGES d D K I T full|L,B\n"); return 2; }
    int d = atoi(argv[3]), D = atoi(argv[4]), T = atoi(argv[7]), full;
    K = atol(argv[5]); I = atol(argv[6]);
    if (K < 1 || I < 0 || I >= K || T < 1 || !parse_layout(argv[8], &full)) { printf("REJECT bad K, I, T or layout\n"); return 2; }
    long *U, *W; uint64_t fp; read_graph(argv[2], &U, &W, &fp);
    if (LB > n) { printf("REJECT layout L*B > n\n"); return 2; }
    st = calloc(n + 1, 8); long *deg = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) {
        if (U[i] == W[i] || U[i] < 0 || W[i] < 0 || U[i] >= n || W[i] >= n) { printf("verdict invalid bad edge %ld\n", i); return 1; }
        deg[U[i]]++; deg[W[i]]++;
    }
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * 8 + 8); long *pos = calloc(n + 1, 8);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    long maxd = 0, mind = n;
    for (long x = 0; x < n; x++) {
        long k = deg[x]; if (k > maxd) maxd = k; if (k < mind) mind = k;
        qsort(adj + st[x], k, 8, cmpl);
        for (long i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) { printf("verdict invalid repeated edge at %ld\n", x); return 1; }
    }
    if (!full) { /* the level shift must map every edge to an edge */
        for (long i = 0; i < m; i++) {
            long pu = U[i] < LB ? (U[i] + B) % LB : U[i], pv = W[i] < LB ? (W[i] + B) % LB : W[i];
            if (!has_edge(pu, pv)) { printf("verdict invalid the level shift is not an automorphism (edge %ld %ld)\n", U[i], W[i]); return 1; }
        }
    }
    int *col = malloc(n * sizeof(int)); for (long i = 0; i < n; i++) col[i] = -1;
    long *q = malloc(n * 8); long h = 0, t = 0; col[0] = 0; q[t++] = 0; int bip = 1;
    while (h < t) { long x = q[h++]; for (long i = st[x]; i < st[x + 1]; i++) { long y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    if (t != n) { printf("verdict invalid disconnected (%ld of %ld)\n", t, n); return 1; }
    nsrc = full ? n : B + (n - LB);
    nbat = (nsrc + 63) / 64;
    ecc = malloc(nbat * sizeof(int)); for (long b = 0; b < nbat; b++) ecc[b] = -1;
    next_b = I;
    pthread_t *th = malloc(T * sizeof(pthread_t));
    for (int i = 0; i < T; i++) pthread_create(&th[i], NULL, work, NULL);
    for (int i = 0; i < T; i++) pthread_join(th[i], NULL);
    if (bad) { printf("verdict invalid unreached vertex in a batch\n"); return 1; }
    printf("apsp-shard-report 1\n");
    printf("graph n %ld m %ld fp %016llx\n", n, m, (unsigned long long)fp);
    printf("params d %d D %d K %ld I %ld layout %s L %ld B %ld nsrc %ld nbatches %ld\n", d, D, K, I, full ? "full" : argv[8],
           full ? 0L : LB / B, B, nsrc, nbat);
    printf("structure simple yes degree %ld %ld bipartite %s connected yes automorphism %s\n", mind, maxd, bip ? "yes" : "no",
           full ? "none" : "checked");
    for (long b = I; b < nbat; b += K) printf("batch %ld ecc %d\n", b, ecc[b]);
    printf("verdict ok\n");
    return 0;
}
static int reject(const char *why) { printf("REJECT %s\n", why); return 1; }
static int run_merge(int argc, char **argv) {
    if (argc < 7) { printf("usage: apsp_shard merge EDGES d D K full|L,B report_0 ... report_{K-1}\n"); return 2; }
    int d = atoi(argv[3]), D = atoi(argv[4]), full; K = atol(argv[5]);
    if (K < 1 || !parse_layout(argv[6], &full)) { printf("REJECT bad K or layout\n"); return 2; }
    if (argc != 7 + K) { printf("REJECT expected %ld reports, got %d\n", K, argc - 7); return 2; }
    long *U, *W; uint64_t fp; read_graph(argv[2], &U, &W, &fp);
    nsrc = full ? n : B + (n - LB);
    nbat = (nsrc + 63) / 64;
    char *seen = calloc(K, 1), *structure = NULL, line[512];
    long nb_seen = 0; int diam = 0, mx_deg = -1, bip = 0; long mn_deg = 0;
    for (long r = 0; r < K; r++) {
        FILE *f = fopen(argv[7 + r], "r");
        if (!f) { printf("REJECT cannot open %s\n", argv[7 + r]); return 2; }
        long rn, rm, rnsrc, rnb, rI, rK, rL, rB; unsigned long long rfp; char rlay[64]; int rd, rD;
        long dmin, dmax; char bp[8], autom[16];
        if (!fgets(line, sizeof line, f) || strcmp(line, "apsp-shard-report 1\n")) { fclose(f); return reject("header") ; }
        if (!fgets(line, sizeof line, f) || sscanf(line, "graph n %ld m %ld fp %llx", &rn, &rm, &rfp) != 3) { fclose(f); return reject("graph line"); }
        if (rn != n || rm != m || rfp != (unsigned long long)fp) { printf("REJECT %s is for another graph\n", argv[7 + r]); return 1; }
        if (!fgets(line, sizeof line, f) || sscanf(line, "params d %d D %d K %ld I %ld layout %63s L %ld B %ld nsrc %ld nbatches %ld",
                &rd, &rD, &rK, &rI, rlay, &rL, &rB, &rnsrc, &rnb) != 9) { fclose(f); return reject("params line"); }
        if (rd != d || rD != D || rK != K || strcmp(rlay, argv[6]) || rnsrc != nsrc || rnb != nbat) { fclose(f); return reject("parameters differ from the merge call"); }
        if (rI < 0 || rI >= K) { fclose(f); return reject("shard index out of range"); }
        if (seen[rI]) { fclose(f); return reject("shard index given twice"); }
        seen[rI] = 1;
        if (!fgets(line, sizeof line, f) || sscanf(line, "structure simple yes degree %ld %ld bipartite %3s connected yes automorphism %15s",
                &dmin, &dmax, bp, autom) != 4) { fclose(f); return reject("structure line"); }
        if (!structure) structure = strdup(line);
        else if (strcmp(structure, line)) { fclose(f); return reject("structure differs between shards"); }
        if (strcmp(autom, strcmp(rlay, "full") ? "checked" : "none")) { fclose(f); return reject("automorphism field does not match the layout"); }
        mn_deg = dmin; mx_deg = (int)dmax; bip = !strcmp(bp, "yes");
        for (long b = rI; b < nbat; b += rK) {
            long rb; int e;
            if (!fgets(line, sizeof line, f) || sscanf(line, "batch %ld ecc %d", &rb, &e) != 2 || rb != b || e < 0) { fclose(f); return reject("batch line"); }
            if (e > diam) diam = e;
            nb_seen++;
        }
        if (!fgets(line, sizeof line, f) || strcmp(line, "verdict ok\n") || fgets(line, sizeof line, f)) { fclose(f); return reject("verdict line or extra lines"); }
        fclose(f);
    }
    for (long r = 0; r < K; r++) if (!seen[r]) { printf("REJECT shard %ld missing\n", r); return 1; }
    if (nb_seen != nbat) { printf("REJECT %ld batches seen, %ld expected\n", nb_seen, nbat); return 1; }
    printf("merged n %ld m %ld fp %016llx shards %ld sources %ld batches %ld diameter %d\n", n, m, (unsigned long long)fp, K, nsrc, nbat, diam);
    printf("degree min %ld max %d bipartite %s\n", mn_deg, mx_deg, bip ? "yes" : "no");
    int ok = bip && mx_deg <= d && diam <= D;
    if (ok) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return ok ? 0 : 1;
}
int main(int argc, char **argv) {
    if (argc < 2) { printf("usage: apsp_shard shard|merge ...\n"); return 2; }
    if (!strcmp(argv[1], "shard")) return run_shard(argc, argv);
    if (!strcmp(argv[1], "merge")) return run_merge(argc, argv);
    printf("unknown mode %s\n", argv[1]); return 2;
}
