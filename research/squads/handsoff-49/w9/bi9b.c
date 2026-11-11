/* bi9: exhaustive / random search over bi-coset graphs (handsoff-49, worker w9).
 * Input BIN (little-endian int32 header, then arrays):
 *   int32 M, int32 h, uint16 T[M*M] (T[c*M+i] = coset of rep_c * rep_i),
 *   int32 Ainv[M*h] (Ainv[c*h+t] = coset of rep_c^-1 * H_t), int32 rho[M*h] (rho[c*h+t] = coset of rep_c * H_t).
 * A choice is a set L of 4 left cosets (c = H s) that is a union of right-H orbits (orbit sizes k_D, sum 4).
 * Graph (n = 2M): A_i ~ B_{T[c][i]} for c in L;  B_j ~ A_{T[c'][j]} for c' in L' = {Ainv[c][t] : c in L, t}.
 * Cost = (far vertices from A0) + (far vertices from B0), far = distance > 9 or unreachable; cost 0 iff diameter <= 9.
 * Usage:
 *   bi9 BIN info
 *   bi9 BIN exh [LIMIT] [OUT]        all L (stop after LIMIT evaluations if LIMIT > 0); OUT: edge list of best L
 *   bi9 BIN rnd COUNT SEED [OUT]     COUNT random L (uniform over orbit-size partitions)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int M, h;
static uint16_t *T, *TB;
static int *Ainv, *rho;
static int norb;
static int *ob, *osz, **omem;          /* orbit id of coset, orbit size, members */
static int *lst[5], nlst[5];           /* orbits of size s (s = 1..4) */
static int *adjA, *adjB, *vis, *q, stamp = 0;
static long long nev = 0;
static int bestcost = 1 << 30, bestL[4];
static int bestpart[8];
static int partcost[5][4000];           /* not used for big spaces; see per-partition minima below */
static int minpart[16]; static int nparts = 0;

static void die(const char *m) { fprintf(stderr, "bi9: %s\n", m); exit(1); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void load(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) die("cannot open bin");
    int32_t hd[2];
    if (fread(hd, 4, 2, f) != 2) die("header");
    M = hd[0]; h = hd[1];
    T = malloc((size_t)M * M * 2);
    Ainv = malloc((size_t)M * h * sizeof(int));
    rho = malloc((size_t)M * h * sizeof(int));
    int32_t *tmp = malloc((size_t)M * h * 4);
    if (fread(T, 2, (size_t)M * M, f) != (size_t)M * M) die("T");
    if (fread(tmp, 4, (size_t)M * h, f) != (size_t)M * h) die("Ainv");
    for (int k = 0; k < M * h; k++) Ainv[k] = tmp[k];
    if (fread(tmp, 4, (size_t)M * h, f) != (size_t)M * h) die("rho");
    for (int k = 0; k < M * h; k++) rho[k] = tmp[k];
    TB = malloc((size_t)M * M * 2);
    if (fread(TB, 2, (size_t)M * M, f) != (size_t)M * M) { memcpy(TB, T, (size_t)M * M * 2); }
    fclose(f); free(tmp);
}

static void orbits(void) {
    ob = malloc(M * sizeof(int)); osz = malloc(M * sizeof(int)); omem = malloc(M * sizeof(int *));
    for (int c = 0; c < M; c++) ob[c] = -1;
    norb = 0;
    int *tmp = malloc(h * sizeof(int));
    for (int c = 0; c < M; c++) if (ob[c] < 0) {
        int nt = 0;
        for (int t = 0; t < h; t++) {
            int v = rho[c * h + t], dup = 0;
            for (int u = 0; u < nt; u++) if (tmp[u] == v) { dup = 1; break; }
            if (!dup) tmp[nt++] = v;
        }
        omem[norb] = malloc(nt * sizeof(int));
        for (int u = 0; u < nt; u++) { omem[norb][u] = tmp[u]; ob[tmp[u]] = norb; }
        osz[norb] = nt; norb++;
    }
    free(tmp);
    for (int s = 1; s <= 4; s++) { lst[s] = malloc((norb + 1) * sizeof(int)); nlst[s] = 0; }
    for (int o = 0; o < norb; o++) if (osz[o] <= 4) lst[osz[o]][nlst[osz[o]]++] = o;
    adjA = malloc((size_t)M * 4 * sizeof(int)); adjB = malloc((size_t)M * 4 * sizeof(int));
    vis = calloc(2 * M, sizeof(int)); q = malloc(2 * M * sizeof(int));
}

/* number of vertices within distance 9 of root (queue after 9 levels) */
static int reach9(int root) {
    stamp++;
    int qh = 0, qt = 0, d = 0;
    q[qt++] = root; vis[root] = stamp;
    while (qh < qt && d < 9) {
        int end = qt;
        while (qh < end) {
            int v = q[qh++];
            if (v < M) {
                for (int k = 0; k < 4; k++) { int w = M + adjA[4 * v + k]; if (vis[w] != stamp) { vis[w] = stamp; q[qt++] = w; } }
            } else {
                int j = v - M;
                for (int k = 0; k < 4; k++) { int w = adjB[4 * j + k]; if (vis[w] != stamp) { vis[w] = stamp; q[qt++] = w; } }
            }
        }
        d++;
    }
    return qt;
}

/* L: 4 left cosets. Returns cost, or -1 if L' does not have 4 cosets (L not right-H-invariant). */
static int evalL(const int *L, int *Lp_out) {
    int Lp[4], np = 0;
    for (int k = 0; k < 4; k++) for (int t = 0; t < h; t++) {
        int v = Ainv[L[k] * h + t], dup = 0;
        for (int u = 0; u < np; u++) if (Lp[u] == v) { dup = 1; break; }
        if (!dup) { if (np == 4) return -1; Lp[np++] = v; }
    }
    if (np != 4) return -1;
    for (int i = 0; i < M; i++) for (int k = 0; k < 4; k++) adjA[4 * i + k] = T[(size_t)L[k] * M + i];
    for (int j = 0; j < M; j++) for (int k = 0; k < 4; k++) adjB[4 * j + k] = TB[(size_t)Lp[k] * M + j];
    int r1 = reach9(0), r2 = reach9(M);
    if (Lp_out) memcpy(Lp_out, Lp, sizeof(Lp));
    nev++;
    return (2 * M - r1) + (2 * M - r2);
}

static int cur[4], ncur;
static int curpart[8], npart;
static int partsize[8];
static int curidx[8];
static char pname[16][16]; static int pnum = 0;
static int bestpartidx;

static void write_edges(const char *out, const int *L) {
    FILE *f = fopen(out, "w");
    if (!f) die("cannot write edges");
    fprintf(f, "%d\n", 2 * M);
    for (int k = 0; k < 4; k++) for (int i = 0; i < M; i++) fprintf(f, "%d %d\n", i, M + T[(size_t)L[k] * M + i]);
    fclose(f);
}

static const char *out_path = NULL;
static long long limit = 0;
static double t0;
static int stopflag = 0;

/* exhaustive recursion over parts (sizes), combinations of distinct orbits of the same size */
static void rec_part(int p, int start) {
    if (stopflag) return;
    if (p == npart) {
        int Lp[4];
        int c = evalL(cur, Lp);
        if (c < 0) return;
        if (c < minpart[bestpartidx]) minpart[bestpartidx] = c;
        if (c < bestcost) {
            bestcost = c; memcpy(bestL, cur, sizeof(cur));
            fprintf(stderr, "  new best cost %d  L={%d,%d,%d,%d} t=%.1fs nev=%lld\n", c, cur[0], cur[1], cur[2], cur[3], now() - t0, nev);
        }
        if (limit > 0 && nev >= limit) stopflag = 1;
        return;
    }
    int s = partsize[p];
    int st = (p > 0 && partsize[p - 1] == s) ? start : 0;
    for (int a = st; a < nlst[s]; a++) {
        int o = lst[s][a];
        /* place the orbit's members: a size-s orbit contributes s cosets; store its first member list */
        for (int u = 0; u < s; u++) cur[ncur + u] = omem[o][u];
        ncur += s;
        rec_part(p + 1, a + 1);
        ncur -= s;
        if (stopflag) return;
    }
}

static long long LIMIT_PART = 300000;
static double combn(int n, int k) { if (k < 0 || n < k) return 0; double r = 1; for (int i = 0; i < k; i++) r = r * (n - i) / (i + 1); return r; }
/* random distinct orbits for the current parts; sets cur[] and ncur (ncur != 4 on failure) */
static void sample_part(void) {
    int ncc = 0;
    for (int p = 0; p < npart; p++) {
        int s = partsize[p];
        for (int tt = 0; tt < 1000; tt++) {
            int o = lst[s][xr() % nlst[s]], dup = 0;
            for (int v = 0; v < ncc; v++) if (ob[cur[v]] == o) dup = 1;
            if (!dup) { for (int v = 0; v < s; v++) cur[ncc + v] = omem[o][v]; ncc += s; break; }
        }
    }
    ncur = ncc;
}
static void enumerate_partitions(void) {
    /* partitions of 4 into orbit sizes, each realised by available orbits */
    int parts[5][4] = { {4}, {3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1} };
    int lens[5] = { 1, 2, 2, 3, 4 };
    for (int pi = 0; pi < 5; pi++) {
        int need[5] = {0, 0, 0, 0, 0};
        for (int u = 0; u < lens[pi]; u++) need[parts[pi][u]]++;
        int ok = 1;
        for (int s = 1; s <= 4; s++) if (need[s] > nlst[s]) ok = 0;
        if (!ok) { minpart[pi] = 1 << 30; continue; }
        /* the parts for rec_part must be non-increasing sizes so that same-size combinations are ordered */
        npart = lens[pi];
        for (int u = 0; u < npart; u++) partsize[u] = parts[pi][u];
        bestpartidx = pi;
        int before = bestcost;
        ncur = 0;
        double cnt = 1;
        for (int s = 1; s <= 4; s++) cnt *= combn(nlst[s], need[s]);
        if (cnt <= (double)LIMIT_PART) {
            rec_part(0, 0);
            fprintf(stderr, "partition exhaustive, count %.0f\n", cnt);
        } else {
            fprintf(stderr, "partition sampled %lld of %.3g\n", LIMIT_PART, cnt);
            for (long long it = 0; it < LIMIT_PART && !stopflag; it++) {
                sample_part();
                if (ncur != 4) continue;
                int Lp[4];
                int c = evalL(cur, Lp);
                if (c < 0) continue;
                if (c < minpart[bestpartidx]) minpart[bestpartidx] = c;
                if (c < bestcost) {
                    bestcost = c; memcpy(bestL, cur, sizeof(cur));
                    fprintf(stderr, "  new best cost %d  L={%d,%d,%d,%d} t=%.1fs nev=%lld\n", c, cur[0], cur[1], cur[2], cur[3], now() - t0, nev);
                }
            }
        }
        fprintf(stderr, "partition {");
        for (int u = 0; u < npart; u++) fprintf(stderr, "%d%s", partsize[u], u + 1 < npart ? "," : "");
        fprintf(stderr, "}: count of orbit choices %s, minimum cost %d (overall best %d)\n",
                "(see nev)", minpart[pi], bestcost);
        (void)before;
        if (stopflag) break;
    }
}

int main(int argc, char **argv) {
    if (argc < 3) die("usage: bi9 BIN info|exh|rnd ...");
    t0 = now();
    load(argv[1]);
    orbits();
    const char *mode = argv[2];
    if (!strcmp(mode, "info")) {
        int cnt[5] = {0, 0, 0, 0, 0};
        for (int o = 0; o < norb; o++) if (osz[o] <= 4) cnt[osz[o]]++;
        int big = 0; for (int o = 0; o < norb; o++) if (osz[o] > 4) big++;
        printf("M=%d h=%d n=%d orbits: size1=%d size2=%d size3=%d size4=%d larger=%d\n",
               M, h, 2 * M, cnt[1], cnt[2], cnt[3], cnt[4], big);
        return 0;
    }
    if (!strcmp(mode, "exh")) {
        if (argc > 3) limit = atoll(argv[3]);
        if (getenv("CAP")) LIMIT_PART = atoll(getenv("CAP"));
        out_path = argc > 4 ? argv[4] : NULL;
        for (int p = 0; p < 16; p++) minpart[p] = 1 << 30;
        enumerate_partitions();
        printf("RESULT_EXH M=%d h=%d n=%d evals=%lld best_cost=%d L=%d,%d,%d,%d time=%.1fs\n", M, h, 2 * M, nev,
               bestcost, bestL[0], bestL[1], bestL[2], bestL[3], now() - t0);
        if (out_path && bestcost < (1 << 30)) write_edges(out_path, bestL);
        return 0;
    }
    if (!strcmp(mode, "rnd")) {
        long long count = argc > 3 ? atoll(argv[3]) : 1000;
        rng ^= (uint64_t)(argc > 4 ? atoll(argv[4]) : 1) * 0x9E3779B97F4A7C15ULL; xr();
        out_path = argc > 5 ? argv[5] : NULL;
        for (long long it = 0; it < count; it++) {
            /* random partition among those realisable, then random distinct orbits */
            int parts[5][4] = { {4}, {3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1} };
            int lens[5] = { 1, 2, 2, 3, 4 };
            int avail[5], na = 0;
            for (int pi = 0; pi < 5; pi++) {
                int need[5] = {0, 0, 0, 0, 0}, ok = 1;
                for (int u = 0; u < lens[pi]; u++) need[parts[pi][u]]++;
                for (int s = 1; s <= 4; s++) if (need[s] > nlst[s]) ok = 0;
                if (ok) avail[na++] = pi;
            }
            if (na == 0) die("no realisable partition");
            int pi = avail[xr() % na];
            int ncc = 0, okk = 1;
            for (int u = 0; u < lens[pi] && okk; u++) {
                int s = parts[pi][u];
                /* pick an orbit of size s not already chosen (compare orbit ids) */
                int chosen = -1;
                for (int tt = 0; tt < 200; tt++) {
                    int o = lst[s][xr() % nlst[s]], dup = 0;
                    for (int v = 0; v < ncc; v++) if (ob[cur[v]] == o) dup = 1;
                    if (!dup) { chosen = o; break; }
                }
                if (chosen < 0) { okk = 0; break; }
                for (int v = 0; v < s; v++) cur[ncc + v] = omem[chosen][v];
                ncc += s;
            }
            if (!okk) continue;
            int c = evalL(cur, NULL);
            if (c >= 0 && c < bestcost) {
                bestcost = c; memcpy(bestL, cur, sizeof(cur));
                fprintf(stderr, "  rnd new best %d L={%d,%d,%d,%d}\n", c, cur[0], cur[1], cur[2], cur[3]);
            }
        }
        printf("RESULT_RND M=%d h=%d n=%d evals=%lld best_cost=%d time=%.1fs\n", M, h, 2 * M, nev, bestcost, now() - t0);
        if (out_path && bestcost < (1 << 30)) { evalL(bestL, NULL); write_edges(out_path, bestL); }
        return 0;
    }
    die("unknown mode");
    return 1;
}
