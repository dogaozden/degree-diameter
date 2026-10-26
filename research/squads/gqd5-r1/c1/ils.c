// ARW-style iterated local search for maximum independent set (partial ovoid of W(9)).
// usage: ils graph.txt seed seconds out.txt
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

static int n;
static int *deg, **adj;
static unsigned char *A;       // adjacency matrix
static int *inS, *tau, *sol, *pos, ssz;
static int best_sz, *best;
static unsigned long long rs;

static inline unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static inline int rndint(int m) { return (int)(rnd() % (unsigned long long)m); }

static void addv(int v) {
    inS[v] = 1; pos[v] = ssz; sol[ssz++] = v;
    for (int k = 0; k < deg[v]; k++) tau[adj[v][k]]++;
}
static void remv(int v) {
    inS[v] = 0;
    int p = pos[v]; int last = sol[--ssz]; sol[p] = last; pos[last] = p;
    for (int k = 0; k < deg[v]; k++) tau[adj[v][k]]--;
}

// add all free vertices (tau==0, not in S), random order
static void fill_free(void) {
    int cnt = 0, *cand = malloc(sizeof(int) * n);
    for (int v = 0; v < n; v++) if (!inS[v] && tau[v] == 0) cand[cnt++] = v;
    while (cnt > 0) {
        int i = rndint(cnt); int v = cand[i]; cand[i] = cand[--cnt];
        if (!inS[v] && tau[v] == 0) addv(v);
        // remaining candidates may still be free; they are checked by tau==0 test
    }
    free(cand);
}

// (1,2)-swap local search until no improving move
static void local_search(void) {
    int improved = 1;
    while (improved) {
        improved = 0;
        fill_free();
        // random order over solution vertices
        int start = ssz ? rndint(ssz) : 0;
        for (int t = 0; t < ssz && !improved; t++) {
            int x = sol[(start + t) % ssz];
            int L[256], m = 0;
            for (int k = 0; k < deg[x]; k++) {
                int u = adj[x][k];
                if (!inS[u] && tau[u] == 1) L[m++] = u;
            }
            if (m < 2) continue;
            // find non-adjacent pair in L (random start)
            int off = rndint(m);
            for (int a = 0; a < m && !improved; a++) {
                int u = L[(a + off) % m];
                for (int b = a + 1; b < m; b++) {
                    int w = L[(b + off) % m];
                    if (!A[(size_t)u * n + w]) {
                        remv(x); addv(u); addv(w);
                        fill_free();
                        improved = 1; break;
                    }
                }
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    rs = strtoull(argv[2], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    double secs = atof(argv[3]);
    if (fscanf(f, "%d", &n) != 1) return 1;
    deg = malloc(sizeof(int) * n); adj = malloc(sizeof(int *) * n);
    A = calloc((size_t)n * n, 1);
    for (int i = 0; i < n; i++) {
        if (fscanf(f, "%d", &deg[i]) != 1) return 1;
        adj[i] = malloc(sizeof(int) * deg[i]);
        for (int k = 0; k < deg[i]; k++) {
            if (fscanf(f, "%d", &adj[i][k]) != 1) return 1;
            A[(size_t)i * n + adj[i][k]] = 1;
        }
    }
    fclose(f);
    inS = calloc(n, sizeof(int)); tau = calloc(n, sizeof(int));
    sol = malloc(sizeof(int) * n); pos = malloc(sizeof(int) * n);
    best = malloc(sizeof(int) * n); best_sz = 0; ssz = 0;
    int *saved = malloc(sizeof(int) * n); int saved_sz;
    for (int i = 0; i < 10; i++) rnd();

    local_search();
    int cur_sz = ssz;
    memcpy(best, sol, sizeof(int) * ssz); best_sz = ssz;
    clock_t t0 = clock();
    long long it = 0, since_best = 0;
    double T = 0.6;
    while (1) {
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > secs) break;
        }
        it++;
        // save current
        saved_sz = ssz; memcpy(saved, sol, sizeof(int) * ssz);
        // perturbation: force-insert 1 (sometimes 2) random non-solution vertices
        int kforce = (rndint(10) == 0) ? 2 : 1;
        for (int r = 0; r < kforce; r++) {
            int v;
            do { v = rndint(n); } while (inS[v]);
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                if (inS[u]) remv(u);
            }
            addv(v);
        }
        local_search();
        int new_sz = ssz;
        if (new_sz > best_sz) {
            best_sz = new_sz; memcpy(best, sol, sizeof(int) * ssz); since_best = 0;
            fprintf(stderr, "it %lld best %d t=%.1f\n", it, best_sz, (double)(clock() - t0) / CLOCKS_PER_SEC);
        } else since_best++;
        // acceptance
        if (new_sz < saved_sz) {
            double d = saved_sz - new_sz;
            double p = exp(-d / T);
            if ((double)(rnd() % 1000000) / 1e6 >= p) {
                // revert
                while (ssz) remv(sol[ssz - 1]);
                for (int i = 0; i < saved_sz; i++) addv(saved[i]);
            }
        }
        cur_sz = ssz;
        // occasional restart from best
        if (since_best > 200000) {
            while (ssz) remv(sol[ssz - 1]);
            for (int i = 0; i < best_sz; i++) addv(best[i]);
            since_best = 0;
        }
    }
    FILE *o = fopen(argv[4], "w");
    fprintf(o, "%d\n", best_sz);
    for (int i = 0; i < best_sz; i++) fprintf(o, "%d ", best[i]);
    fprintf(o, "\n");
    fclose(o);
    printf("RESULT best=%d iters=%lld\n", best_sz, it);
    return 0;
}
