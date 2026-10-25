/* ils.c: ARW-style iterated local search for a maximum independent set in the orbit conflict graph (all orbits have
   the same size, so the weight is size * |S|).  State S is always independent.  tight[v] = #neighbours of v in S;
   xs[v] = XOR of those neighbours (the unique one when tight[v] = 1).  Local search: free insertions, and (1,2)-swaps
   at a solution vertex x that has two non-adjacent 1-tight neighbours.  Perturbation: force-insert a random outside
   vertex of small tightness (removing its solution neighbours), then local search.  Changes since the perturbation
   are logged and undone when the result is smaller (with a small acceptance probability for smaller results).
   usage: ils GRAPH.bin START.txt|- SEED SECONDS OUT.txt [TMAX] [ACCEPT_PER_MILLE]     (OUT: best set, vertex ids) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int nv; static int64_t M2;
static int64_t *off; static int32_t *adj;
static char *insol, *inQ, *inF;
static int *tight, *xs, *S, *pos, ns;
static int *Q, nq, *F, nf, *C;
static int *logv; static signed char *logop; static int64_t nlog, logcap; static int logging = 0, pushing = 1;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int adjacent(int u, int v) {
    int64_t lo = off[u], hi = off[u + 1] - 1;
    while (lo <= hi) {
        int64_t mid = (lo + hi) >> 1; int32_t x = adj[mid];
        if (x == v) return 1;
        if (x < v) lo = mid + 1; else hi = mid - 1;
    }
    return 0;
}
static void logop_push(int v, int op) {
    if (nlog == logcap) { logcap = logcap ? 2 * logcap : 1 << 16; logv = realloc(logv, logcap * sizeof(int)); logop = realloc(logop, logcap); }
    logv[nlog] = v; logop[nlog] = (signed char)op; nlog++;
}
static void pushQ(int x) { if (pushing && !inQ[x]) { inQ[x] = 1; Q[nq++] = x; } }
static void pushF(int u) { if (pushing && !inF[u]) { inF[u] = 1; F[nf++] = u; } }
static void add_s(int v) {
    insol[v] = 1; pos[v] = ns; S[ns++] = v;
    for (int64_t t = off[v]; t < off[v + 1]; t++) { int u = adj[t]; tight[u]++; xs[u] ^= v; }
    if (logging) logop_push(v, 1);
    pushQ(v);
}
static void rem_s(int v) {
    insol[v] = 0; int p = pos[v]; int last = S[--ns]; S[p] = last; pos[last] = p;
    for (int64_t t = off[v]; t < off[v + 1]; t++) {
        int u = adj[t]; tight[u]--; xs[u] ^= v;
        if (!insol[u]) { if (tight[u] == 0) pushF(u); else if (tight[u] == 1) pushQ(xs[u]); }
    }
    if (logging) logop_push(v, -1);
}
static void local_search(void) {
    for (;;) {
        while (nf) { int u = F[--nf]; inF[u] = 0; if (!insol[u] && tight[u] == 0) add_s(u); }
        if (!nq) break;
        int x = Q[--nq]; inQ[x] = 0;
        if (!insol[x]) continue;
        int nc = 0;
        for (int64_t t = off[x]; t < off[x + 1]; t++) { int u = adj[t]; if (!insol[u] && tight[u] == 1) C[nc++] = u; }
        if (nc < 2) continue;
        int a = -1, b = -1;
        for (int i = 0; i < nc && a < 0; i++)
            for (int j = i + 1; j < nc; j++) if (!adjacent(C[i], C[j])) { a = C[i]; b = C[j]; break; }
        if (a < 0) continue;
        rem_s(x); add_s(a); add_s(b);
    }
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void save(const char *fn) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *fo = fopen(tmp, "w"); if (!fo) return;
    for (int i = 0; i < ns; i++) fprintf(fo, "%d\n", S[i]);
    fclose(fo); rename(tmp, fn);
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ils GRAPH.bin START.txt|- SEED SECONDS OUT.txt [TMAX] [ACCEPT_PER_MILLE]\n"); return 1; }
    const char *gfile = argv[1], *startf = argv[2], *outf = argv[5];
    rs = 0x2545F4914F6CDD1DULL ^ ((uint64_t)strtoull(argv[3], 0, 10) * 0x9E3779B97F4A7C15ULL); if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]);
    int TMAX = argc > 6 ? atoi(argv[6]) : 2, ACC = argc > 7 ? atoi(argv[7]) : 2;
    FILE *fp = fopen(gfile, "rb"); if (!fp) { perror("graph"); return 1; }
    int64_t hdr[2]; if (fread(hdr, 8, 2, fp) != 2) return 1; nv = (int)hdr[0]; M2 = hdr[1];
    off = malloc((size_t)(nv + 1) * 8); adj = malloc((size_t)M2 * 4);
    if (fread(off, 8, nv + 1, fp) != (size_t)nv + 1 || fread(adj, 4, M2, fp) != (size_t)M2) { fprintf(stderr, "short read\n"); return 1; }
    fclose(fp);
    insol = calloc(nv, 1); inQ = calloc(nv, 1); inF = calloc(nv, 1);
    tight = calloc(nv, sizeof(int)); xs = calloc(nv, sizeof(int)); S = malloc(nv * sizeof(int)); pos = malloc(nv * sizeof(int));
    Q = malloc(nv * sizeof(int)); F = malloc(nv * sizeof(int)); C = malloc(nv * sizeof(int));
    ns = 0; nq = 0; nf = 0; nlog = 0;
    if (strcmp(startf, "-") != 0) {
        FILE *fs = fopen(startf, "r"); if (!fs) { perror("start"); return 1; }
        int v; while (fscanf(fs, "%d", &v) == 1) if (v >= 0 && v < nv && !insol[v] && tight[v] == 0) add_s(v);
        fclose(fs);
    }
    for (int v = 0; v < nv; v++) if (!insol[v] && tight[v] == 0) pushF(v);
    local_search();
    int best = ns; save(outf); int dirty = 0; double tsave = now();
    fprintf(stderr, "nv %d start |S| %d\n", nv, ns);
    logging = 1; pushing = 1;
    double t0 = now(), tlog = t0; long long it = 0, nundo = 0, nacc = 0;
    for (;;) {
        if ((it & 1023) == 0) {
            double t = now();
            if (t - t0 > secs) break;
            if (dirty && t - tsave > 1.0) { save(outf); dirty = 0; tsave = t; }
            if (t - tlog > 30.0) { fprintf(stderr, "t=%.0f it=%lld cur=%d best=%d undo=%lld acc_worse=%lld\n", t - t0, it, ns, best, nundo, nacc); tlog = t; }
        }
        it++;
        int old = ns; nlog = 0;
        /* perturbation: force-insert a random outside vertex of small tightness */
        int v = -1;
        for (int tries = 0; tries < 400; tries++) {
            int c = (int)(rnd() % (uint64_t)nv);
            if (insol[c]) continue;
            if (v < 0 || tight[c] < tight[v]) v = c;
            if (tight[c] <= TMAX) break;
        }
        if (v < 0) continue;
        for (int64_t t = off[v]; t < off[v + 1]; t++) { int w = adj[t]; if (insol[w]) rem_s(w); }
        add_s(v);
        local_search();
        if (ns > best) { best = ns; dirty = 1; fprintf(stderr, "IMPROVED best %d at it=%lld t=%.1fs\n", best, it, now() - t0); }
        if (ns < old) {
            if ((int)(rnd() % 1000) >= ACC) {        /* undo everything since the perturbation */
                nundo++;
                pushing = 0; logging = 0;
                for (int64_t i = nlog - 1; i >= 0; i--) { if (logop[i] > 0) rem_s(logv[i]); else add_s(logv[i]); }
                pushing = 1; logging = 1;
            } else nacc++;
        }
        nlog = 0;
    }
    if (dirty) save(outf);
    fprintf(stderr, "DONE it=%lld best=%d cur=%d undo=%lld acc_worse=%lld time=%.1fs\n", it, best, ns, nundo, nacc, now() - t0);
    printf("%d\n", best);
    return 0;
}
