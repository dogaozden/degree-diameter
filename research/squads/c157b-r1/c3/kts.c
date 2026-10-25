/* kts.c: k-fixed min-conflict tabu search for a large independent set in an orbit conflict graph (vertices = line
   orbits, edge = some line of one orbit meets some line of the other; all orbits have equal size, so the weight
   sum is size * |S|).  State: S, f = number of edges inside S.  A step removes the vertex u of S with the most
   neighbours in S (non-tabu, random ties) and adds the vertex v outside S with the fewest neighbours in S
   (non-tabu, random ties); delta f = conf[v] - adj(u,v) - conf[u].  When f = 0, S is independent: it is written to
   OUT and |S| is increased by one (add the outside vertex with fewest neighbours in S).
   usage: kts GRAPH.bin START.txt|- SEED SECONDS OUT.txt [K0] [TT]
   START.txt lists vertex ids (may be "-" for a greedy random start of size K0). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int nv;
static int64_t M2;
static int64_t *off;
static int32_t *adj;
static int *conf, *S, *posS, ks;
static char *inS;
static long long *tabu;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndn(int n) { return (int)(rnd() % (uint64_t)n); }

static int adjacent(int u, int v) {
    int64_t lo = off[u], hi = off[u + 1] - 1;
    while (lo <= hi) {
        int64_t mid = (lo + hi) >> 1; int32_t x = adj[mid];
        if (x == v) return 1;
        if (x < v) lo = mid + 1; else hi = mid - 1;
    }
    return 0;
}
static void add_v(int v) {
    inS[v] = 1; posS[v] = ks; S[ks++] = v;
    for (int64_t t = off[v]; t < off[v + 1]; t++) conf[adj[t]]++;
}
static void rem_v(int v) {
    inS[v] = 0; int p = posS[v]; int last = S[--ks]; S[p] = last; posS[last] = p;
    for (int64_t t = off[v]; t < off[v + 1]; t++) conf[adj[t]]--;
}
/* outside vertex with fewest neighbours in S; non-tabu unless all are tabu */
static int pick_min_out(long long it) {
    int best = -1, bc = 1 << 30, cnt = 0;
    for (int pass = 0; pass < 2 && best < 0; pass++) {
        for (int v = 0; v < nv; v++) {
            if (inS[v]) continue;
            if (pass == 0 && tabu[v] > it) continue;
            int c = conf[v];
            if (c < bc) { bc = c; best = v; cnt = 1; }
            else if (c == bc && rndn(++cnt) == 0) best = v;
        }
    }
    return best;
}
/* vertex of S with most neighbours in S (conflicting), non-tabu unless all conflicting ones are tabu */
static int pick_max_in(long long it) {
    int best = -1, bc = -1, cnt = 0;
    for (int pass = 0; pass < 2 && best < 0; pass++) {
        for (int i = 0; i < ks; i++) {
            int u = S[i];
            if (conf[u] == 0) continue;
            if (pass == 0 && tabu[u] > it) continue;
            int c = conf[u];
            if (c > bc) { bc = c; best = u; cnt = 1; }
            else if (c == bc && rndn(++cnt) == 0) best = u;
        }
    }
    return best;
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void save(const char *fn) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *fo = fopen(tmp, "w"); if (!fo) return;
    for (int i = 0; i < ks; i++) fprintf(fo, "%d\n", S[i]);
    fclose(fo); rename(tmp, fn);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: kts GRAPH.bin START.txt|- SEED SECONDS OUT.txt [K0] [TT]\n"); return 1; }
    const char *gfile = argv[1], *startf = argv[2], *outf = argv[5];
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)strtoull(argv[3], 0, 10) * 2654435761ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]);
    int K0 = argc > 6 ? atoi(argv[6]) : 0, TT = argc > 7 ? atoi(argv[7]) : 10;
    FILE *fp = fopen(gfile, "rb"); if (!fp) { perror("graph"); return 1; }
    int64_t hdr[2]; if (fread(hdr, 8, 2, fp) != 2) return 1; nv = (int)hdr[0]; M2 = hdr[1];
    off = malloc((size_t)(nv + 1) * 8); adj = malloc((size_t)M2 * 4);
    if (fread(off, 8, nv + 1, fp) != (size_t)nv + 1 || fread(adj, 4, M2, fp) != (size_t)M2) { fprintf(stderr, "short read\n"); return 1; }
    fclose(fp);
    conf = calloc(nv, sizeof(int)); S = malloc(nv * sizeof(int)); posS = malloc(nv * sizeof(int));
    inS = calloc(nv, 1); tabu = calloc(nv, sizeof(long long));
    ks = 0;
    if (strcmp(startf, "-") != 0) {
        FILE *fs = fopen(startf, "r"); if (!fs) { perror("start"); return 1; }
        int v; while (fscanf(fs, "%d", &v) == 1) if (v >= 0 && v < nv && !inS[v]) add_v(v);
        fclose(fs);
    }
    while (ks < K0) add_v(pick_min_out(0));
    long long f = 0;
    for (int i = 0; i < ks; i++) f += conf[S[i]];
    f /= 2;
    fprintf(stderr, "nv %d edges %lld start |S| %d f %lld\n", nv, (long long)(M2 / 2), ks, f);
    int bestks = 0; long long it = 0, lastlog = 0, nfound = 0;
    double t0 = now(), tlast = t0; long long minf = f; long long minf_it = 0;
    while (1) {
        if ((it & 4095) == 0) {
            double t = now();
            if (t - t0 > secs) break;
            if (t - tlast > 30.0) {
                fprintf(stderr, "t=%.0fs it=%lld ks=%d f=%lld minf(at this size)=%lld bestks=%d\n", t - t0, it, ks, f, minf, bestks);
                tlast = t;
            }
        }
        if (f == 0) {
            if (ks > bestks) {
                bestks = ks; save(outf); nfound++;
                fprintf(stderr, "FOUND independent set of size %d at it=%lld t=%.1fs\n", ks, it, now() - t0);
            }
            int v = pick_min_out(it);
            f += conf[v];
            add_v(v);
            minf = f; minf_it = it;
            (void)minf_it;
            it++;
            continue;
        }
        int u = pick_max_in(it);
        int v = pick_min_out(it);
        int d = conf[v] - adjacent(u, v) - conf[u];
        rem_v(u); add_v(v); f += d;
        tabu[u] = it + TT + rndn(TT);
        tabu[v] = it + 1 + rndn(2);
        if (f < minf) { minf = f; minf_it = it; }
        it++;
        (void)lastlog;
    }
    if (bestks > 0) {
        /* check final validity of the best saved file is done by the caller (chkset) */
    }
    fprintf(stderr, "DONE it=%lld bestks=%d found=%lld ks=%d f=%lld time=%.1fs\n", it, bestks, nfound, ks, f, now() - t0);
    printf("%d\n", bestks);
    return 0;
}
