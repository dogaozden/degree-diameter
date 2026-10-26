// c48: simulated annealing over 4-regular simple bipartite graphs (no group).
// Move: 2-switch (a-b, c-d) -> (a-d, c-b), keeps bipartite + degrees.
// Cost: number of unordered pairs at distance > 8 (bitset BFS, all pairs).
// usage: sa N SECS SEED T0 T1 OUT.edges
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define D 4
#define RAD 8
#define MAXN 2400
#define MAXW 40

static int n, h, Wd;
static int adj[MAXN][D];
static uint64_t *Rb, *Rn;
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static long far_count(void){
    for (int v = 0; v < n; v++) {
        uint64_t *r = Rb + (size_t)v * Wd;
        memset(r, 0, sizeof(uint64_t) * Wd);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < RAD; k++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = Rn + (size_t)v * Wd;
            memcpy(dst, Rb + (size_t)v * Wd, sizeof(uint64_t) * Wd);
            for (int i = 0; i < D; i++) {
                const uint64_t *src = Rb + (size_t)adj[v][i] * Wd;
                for (int w = 0; w < Wd; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = Rb; Rb = Rn; Rn = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int pop = 0;
        const uint64_t *r = Rb + (size_t)v * Wd;
        for (int w = 0; w < Wd; w++) pop += __builtin_popcountll(r[w]);
        tot += n - pop;
    }
    return tot / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < D; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void replace_nb(int v, int old, int nw) {
    for (int i = 0; i < D; i++) if (adj[v][i] == old) { adj[v][i] = nw; return; }
    fprintf(stderr, "internal: replace failed\n"); exit(2);
}

static int init_random(void) {
    // 4 random perfect matchings A(0..h-1) -> B(h..n-1), no repeated edge
    int perm[MAXN];
    for (int a = 0; a < h; a++) for (int i = 0; i < D; i++) adj[a][i] = -1;
    for (int layer = 0; layer < D; layer++) {
        int ok = 0;
        for (int tries = 0; tries < 100000 && !ok; tries++) {
            for (int i = 0; i < h; i++) perm[i] = i;
            for (int i = h - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
            ok = 1;
            for (int a = 0; a < h && ok; a++)
                for (int l = 0; l < layer; l++) if (adj[a][l] == h + perm[a]) { ok = 0; break; }
        }
        if (!ok) return 0;
        for (int a = 0; a < h; a++) adj[a][layer] = h + perm[a];
    }
    for (int b = h; b < n; b++) for (int i = 0; i < D; i++) adj[b][i] = -1;
    for (int a = 0; a < h; a++) for (int i = 0; i < D; i++) {
        int b = adj[a][i];
        int placed = 0;
        for (int j = 0; j < D; j++) if (adj[b][j] == -1) { adj[b][j] = a; placed = 1; break; }
        if (!placed) return 0;
    }
    return 1;
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) { perror("open"); exit(1); }
    fprintf(f, "%d\n", n);
    for (int a = 0; a < h; a++) for (int i = 0; i < D; i++) fprintf(f, "%d %d\n", a, adj[a][i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: sa N SECS SEED T0 T1 OUT.edges\n"); return 1; }
    n = atoi(argv[1]);
    double secs = atof(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[3]) * 2654435761ULL;
    for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    const char *out = argv[6];
    if (n > MAXN || (n & 1)) { fprintf(stderr, "bad n\n"); return 1; }
    h = n / 2;
    Wd = (n + 63) / 64;
    Rb = calloc((size_t)n * Wd, sizeof(uint64_t));
    Rn = calloc((size_t)n * Wd, sizeof(uint64_t));
    if (!init_random()) { fprintf(stderr, "init failed\n"); return 1; }

    long cur = far_count();
    long best = cur;
    int bestadj[MAXN][D];
    memcpy(bestadj, adj, sizeof(adj));
    fprintf(stderr, "init far=%ld\n", cur);

    double t0 = now(), tend = t0 + secs;
    long it = 0, acc = 0, evals = 0;
    double T = T0;
    while (1) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= tend) break;
            double frac = (tn - t0) / secs;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        int a = rnd() % h, c = rnd() % h;
        if (a == c) continue;
        int i = rnd() % D, j = rnd() % D;
        int b = adj[a][i], d = adj[c][j];
        if (b == d) continue;
        if (has_edge(a, d) || has_edge(c, b)) continue;
        // save rows
        int sa_[D], sc_[D], sb_[D], sd_[D];
        memcpy(sa_, adj[a], sizeof sa_); memcpy(sc_, adj[c], sizeof sc_);
        memcpy(sb_, adj[b], sizeof sb_); memcpy(sd_, adj[d], sizeof sd_);
        adj[a][i] = d; adj[c][j] = b;
        replace_nb(b, a, c);
        replace_nb(d, c, a);
        long nf = far_count(); evals++;
        long delta = nf - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nf; acc++;
            if (cur < best) {
                best = cur;
                memcpy(bestadj, adj, sizeof(adj));
                if (best == 0) break;
            }
        } else {
            memcpy(adj[a], sa_, sizeof sa_); memcpy(adj[c], sc_, sizeof sc_);
            memcpy(adj[b], sb_, sizeof sb_); memcpy(adj[d], sd_, sizeof sd_);
        }
        if (evals % 2000 == 0) fprintf(stderr, "evals=%ld cur=%ld best=%ld T=%.3f acc=%ld\n", evals, cur, best, T, acc);
    }
    memcpy(adj, bestadj, sizeof(adj));
    // rebuild B rows consistency is implicit (only A rows stored in bestadj copy, B rows also copied)
    long chk = far_count();
    printf("RESULT n=%d evals=%ld best=%ld check=%ld miss=%.4f secs=%.1f\n", n, evals, best, chk, 2.0 * chk / n, now() - t0);
    write_edges(out);
    return 0;
}
