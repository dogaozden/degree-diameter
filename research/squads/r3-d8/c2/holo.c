/* holo.c -- Z_K holonomy design of flag voltages on the incidence graph of the split Cayley hexagon H(q).
 *
 * Points are 0..N-1, lines N..2N-1; flag f = k*G+j (G = q+1) joins point lp[k*G+j] to line N+k.
 * Dart point->line carries +vol[f] in Z_K, line->point carries -vol[f].  An opposite pair is two points (or two
 * lines) at incidence distance 6; the G geodesics between them are the length-6 paths.  A pair is GOOD when its
 * geodesics carry >= K-1 distinct voltages; deficiency(pair) = max(0, K-1-distinct).
 *
 *   holo anneal GH K SEED ITERS NSAMPLE T0 T1 OUT
 *       Metropolis annealing of flag voltages on the geodesic records of NSAMPLE random sources (0 or >= 2N = all).
 *       A pair is recorded once: (s,t) with s sampled and (t not sampled or s < t).  Writes OUT (one voltage per
 *       flag, line by line, flag index f = k*G+j).  Prints sample statistics and exact statistics over all sources
 *       for the random start and for the result.
 *   holo eval GH K VOL|random:SEED
 *       exact statistics over all sources (DP over the set of geodesic voltages).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, N, NV, G, F, K;
static int *lp, *ast, *av, *af, *dist, *queue, *insamp, *pidt, *cntt;
static long long P, R, pcur;
static uint16_t *rf;      /* R*6: flag*2 + (dart point->line) */
static uint8_t *rv, *pdef; /* rv[R] voltage of record, pdef[P] deficiency of pair */
static long long *ist;     /* inverse index starts, size F+1 */
static uint32_t *ient;     /* inverse entries: record*2 + (dart point->line) */
static int pathf[6], paths[6];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urnd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int irnd(int n) { return (int)(urnd() * n); }

static void read_gh(const char *path) {
    FILE *fh = fopen(path, "r");
    if (!fh) { perror(path); exit(1); }
    if (fscanf(fh, "%d %d", &q, &N) != 2) { fprintf(stderr, "bad header\n"); exit(1); }
    G = q + 1; NV = 2 * N; F = N * G;
    lp = malloc(sizeof(int) * F);
    for (int i = 0; i < F; i++) if (fscanf(fh, "%d", &lp[i]) != 1) { fprintf(stderr, "bad body\n"); exit(1); }
    fclose(fh);
}

static void build_adj(void) {
    int *deg = calloc(NV, sizeof(int));
    for (int k = 0; k < N; k++) for (int j = 0; j < G; j++) { deg[lp[k*G+j]]++; deg[N+k]++; }
    for (int x = 0; x < NV; x++) if (deg[x] != G) { fprintf(stderr, "degree %d at %d\n", deg[x], x); exit(1); }
    ast = malloc(sizeof(int) * (NV + 1)); ast[0] = 0;
    for (int x = 0; x < NV; x++) ast[x+1] = ast[x] + deg[x];
    av = malloc(sizeof(int) * ast[NV]); af = malloc(sizeof(int) * ast[NV]);
    int *fill = calloc(NV, sizeof(int));
    for (int k = 0; k < N; k++) for (int j = 0; j < G; j++) {
        int p = lp[k*G+j], L = N + k, f = k*G + j;
        int i = ast[p] + fill[p]++; av[i] = L; af[i] = f;
        i = ast[L] + fill[L]++; av[i] = p; af[i] = f;
    }
    free(deg); free(fill);
    dist = malloc(sizeof(int) * NV); queue = malloc(sizeof(int) * NV);
    pidt = malloc(sizeof(int) * NV); cntt = malloc(sizeof(int) * NV);
}

static void bfs(int s) {
    for (int x = 0; x < NV; x++) dist[x] = -1;
    int h = 0, t = 0; dist[s] = 0; queue[t++] = s;
    while (h < t) {
        int x = queue[h++];
        for (int e = ast[x]; e < ast[x+1]; e++) { int y = av[e]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } }
    }
}

static int cond(int s, int t) { return !insamp[t] || s < t; }

static void dfs_rec(int x, int d) {
    if (d == 6) {
        int pid = pidt[x];
        if (pid >= 0) {
            if (cntt[x] >= G) { fprintf(stderr, "too many geodesics\n"); exit(1); }
            long long r = (long long)pid * G + cntt[x]++;
            for (int i = 0; i < 6; i++) rf[r*6 + i] = (uint16_t)(pathf[i]*2 + (paths[i] > 0));
        }
        return;
    }
    for (int e = ast[x]; e < ast[x+1]; e++) {
        int y = av[e];
        if (dist[y] == d + 1) { pathf[d] = af[e]; paths[d] = (x < N) ? 1 : -1; dfs_rec(y, d + 1); }
    }
}

/* pass 0 counts pairs, pass 1 fills records (G geodesics per pair, 6 darts each) */
static void records_pass(int fill) {
    if (!fill) {
        P = 0;
        for (int s = 0; s < NV; s++) {
            if (!insamp[s]) continue;
            bfs(s);
            for (int t = 0; t < NV; t++) if (dist[t] == 6 && cond(s, t)) P++;
        }
        return;
    }
    pcur = 0;
    for (int s = 0; s < NV; s++) {
        if (!insamp[s]) continue;
        bfs(s);
        for (int t = 0; t < NV; t++) {
            if (dist[t] == 6 && cond(s, t)) pidt[t] = (int)(pcur++); else pidt[t] = -1;
            cntt[t] = 0;
        }
        dfs_rec(s, 0);
        for (int t = 0; t < NV; t++) if (pidt[t] >= 0 && cntt[t] != G) { fprintf(stderr, "geodesics %d != G\n", cntt[t]); exit(1); }
    }
    if (pcur != P) { fprintf(stderr, "pair count mismatch\n"); exit(1); }
}

static void compute_rv(const int *vol) {
    for (long long r = 0; r < R; r++) {
        int s = 0;
        for (int i = 0; i < 6; i++) { int code = rf[r*6 + i]; int f = code >> 1; s += (code & 1) ? vol[f] : -vol[f]; }
        s %= K; if (s < 0) s += K;
        rv[r] = (uint8_t)s;
    }
    for (long long p = 0; p < P; p++) {
        uint32_t m = 0;
        for (int j = 0; j < G; j++) m |= 1u << rv[p*G + j];
        int d = K - 1 - __builtin_popcount(m);
        pdef[p] = (uint8_t)(d > 0 ? d : 0);
    }
}

static void build_inverse(void) {
    ist = calloc(F + 1, sizeof(long long));
    for (long long r = 0; r < R; r++) for (int i = 0; i < 6; i++) ist[(rf[r*6 + i] >> 1) + 1]++;
    for (int f = 0; f < F; f++) ist[f+1] += ist[f];
    ient = malloc(sizeof(uint32_t) * (size_t)(R * 6));
    long long *fp = malloc(sizeof(long long) * F);
    memcpy(fp, ist, sizeof(long long) * F);
    for (long long r = 0; r < R; r++) for (int i = 0; i < 6; i++) {
        int code = rf[r*6 + i], f = code >> 1;
        ient[fp[f]++] = (uint32_t)(r * 2 + (code & 1));
    }
    free(fp);
}

static void sample_hist(long long *hist) {
    for (int d = 0; d <= K; d++) hist[d] = 0;
    for (long long p = 0; p < P; p++) {
        uint32_t m = 0;
        for (int j = 0; j < G; j++) m |= 1u << rv[p*G + j];
        hist[__builtin_popcount(m)]++;
    }
}

static void print_hist(const char *tag, long long *hist, long long total) {
    long long bad = 0;
    for (int d = 1; d < K - 1; d++) bad += hist[d];
    printf("%s pairs=%lld distinct_hist:", tag, total);
    for (int d = 1; d <= K; d++) printf(" d%d=%lld", d, hist[d]);
    printf(" bad(<K-1)=%lld frac=%.5f\n", bad, total ? (double)bad / (double)total : 0.0);
}

static long long anneal(long long iters, double T0, double T1, int *vol) {
    long long cost = 0, nbad = 0;
    for (long long p = 0; p < P; p++) { cost += pdef[p]; if (pdef[p]) nbad++; }
    long long maxinv = 0;
    for (int f = 0; f < F; f++) if (ist[f+1] - ist[f] > maxinv) maxinv = ist[f+1] - ist[f];
    uint8_t *told = malloc(maxinv + 1);
    int *aff = malloc(sizeof(int) * (maxinv + 1)), *newd = malloc(sizeof(int) * (maxinv + 1));
    int *stamp = calloc(P + 1, sizeof(int));
    int sv = 0;
    double lr = log(T1 / T0);
    for (long long it = 0; it < iters; it++) {
        double T = T0 * exp(lr * (double)it / (double)iters);
        int f = irnd(F), old = vol[f];
        int nv = (old + 1 + irnd(K - 1)) % K;
        int sh = (nv - old + K) % K;
        long long a0 = ist[f], nrec = ist[f+1] - a0;
        sv++;
        int naff = 0;
        for (long long i = 0; i < nrec; i++) {
            uint32_t e = ient[a0 + i], r = e >> 1; int pos = (int)(e & 1);
            told[i] = rv[r];
            int dd = pos ? sh : (K - sh) % K;
            rv[r] = (uint8_t)((rv[r] + dd) % K);
            long long p = r / G;
            if (stamp[p] != sv) { stamp[p] = sv; aff[naff++] = (int)p; }
        }
        long long dcost = 0; long long dbad = 0;
        for (int a = 0; a < naff; a++) {
            long long p = aff[a]; uint32_t m = 0;
            for (int j = 0; j < G; j++) m |= 1u << rv[p*G + j];
            int d = K - 1 - __builtin_popcount(m); if (d < 0) d = 0;
            newd[a] = d;
            dcost += d - pdef[p];
            dbad += (d > 0) - (pdef[p] > 0);
        }
        int acc = (dcost <= 0) || (urnd() < exp(-(double)dcost / T));
        if (acc) {
            vol[f] = nv;
            for (int a = 0; a < naff; a++) pdef[aff[a]] = (uint8_t)newd[a];
            cost += dcost; nbad += dbad;
        } else {
            for (long long i = 0; i < nrec; i++) { uint32_t r = ient[a0 + i] >> 1; rv[r] = told[i]; }
        }
        if ((it & 0x3FFFF) == 0) fprintf(stderr, "  it %lld T %.3f cost %lld bad %lld\n", it, T, cost, nbad);
    }
    free(told); free(aff); free(newd); free(stamp);
    return nbad;
}

/* exact statistics over all ordered opposite pairs via DP over geodesic voltage sets */
static void exact_eval(const int *vol, long long *hist, long long *npairs, long long *geod_viol) {
    uint32_t full = (K >= 32) ? 0xffffffffu : ((1u << K) - 1);
    uint32_t *mask = malloc(sizeof(uint32_t) * NV);
    int *cg = malloc(sizeof(int) * NV);
    for (int s = 0; s < NV; s++) {
        bfs(s);
        for (int x = 0; x < NV; x++) { mask[x] = 0; cg[x] = 0; }
        mask[s] = 1; cg[s] = 1;
        for (int h = 0; h < NV; h++) {
            int x = queue[h];
            if (dist[x] >= 6) continue;
            for (int e = ast[x]; e < ast[x+1]; e++) {
                int y = av[e];
                if (dist[y] != dist[x] + 1) continue;
                int f = af[e];
                int sh = (x < N) ? vol[f] % K : (K - vol[f] % K) % K;
                uint32_t m = mask[x];
                uint32_t rot = sh ? (((m << sh) | (m >> (K - sh))) & full) : m;
                mask[y] |= rot;
                cg[y] += cg[x];
            }
        }
        for (int t = 0; t < NV; t++) {
            if (dist[t] == 6) { hist[__builtin_popcount(mask[t])]++; (*npairs)++; if (cg[t] != G) (*geod_viol)++; }
            else if (dist[t] < 6 && cg[t] != 1) (*geod_viol)++;
        }
    }
    free(mask); free(cg);
}

/* WalkSAT-style repair: pick a random bad pair, one of its 6 flags on one of its geodesics, and move that flag to the
 * value minimising the total deficiency (noise: random value).  Keeps the best state seen. */
static long long *bad_list, *bad_pos, nbadl;
static void bad_set(long long p, int bad) {
    if (bad && bad_pos[p] < 0) { bad_pos[p] = nbadl; bad_list[nbadl++] = p; }
    else if (!bad && bad_pos[p] >= 0) {
        long long i = bad_pos[p], last = bad_list[--nbadl];
        bad_list[i] = last; bad_pos[last] = i; bad_pos[p] = -1;
    }
}
static void walk(long long steps, double noise, int *vol, int *vol_best) {
    bad_list = malloc(sizeof(long long) * (P + 1)); bad_pos = malloc(sizeof(long long) * (P + 1)); nbadl = 0;
    for (long long p = 0; p < P; p++) { bad_pos[p] = -1; if (pdef[p]) bad_set(p, 1); }
    long long best = nbadl;
    memcpy(vol_best, vol, sizeof(int) * F);
    for (long long st = 0; st < steps && nbadl > 0; st++) {
        long long p = bad_list[(long long)(urnd() * nbadl)];
        int j = irnd(G), i = irnd(6);
        long long r = p * G + j;
        int f = rf[r*6 + i] >> 1;
        int old = vol[f];
        int cand[64]; int dc[64]; int nc = 0;
        long long a0 = ist[f], nrec = ist[f+1] - a0;
        for (int nv = 0; nv < K; nv++) {
            if (nv == old) continue;
            int sh = (nv - old + K) % K;
            long long dcost = 0;
            for (long long t = 0; t < nrec; t++) {
                uint32_t e = ient[a0 + t], r2 = e >> 1; int pos = (int)(e & 1);
                long long p2 = r2 / G; int j2 = (int)(r2 - p2 * G);
                int dd = pos ? sh : (K - sh) % K;
                int newv = (rv[r2] + dd) % K;
                uint32_t m = 1u << newv;
                for (int jj = 0; jj < G; jj++) if (jj != j2) m |= 1u << rv[p2*G + jj];
                int d = K - 1 - __builtin_popcount(m); if (d < 0) d = 0;
                dcost += d - pdef[p2];
            }
            cand[nc] = nv; dc[nc] = (int)dcost; nc++;
        }
        int pick = 0;
        if (urnd() < noise) pick = irnd(nc);
        else {
            int bestd = 1 << 30, cntb = 0;
            for (int c = 0; c < nc; c++) {
                if (dc[c] < bestd) { bestd = dc[c]; pick = c; cntb = 1; }
                else if (dc[c] == bestd) { cntb++; if (irnd(cntb) == 0) pick = c; }
            }
        }
        int nv = cand[pick], sh = (nv - old + K) % K;
        for (long long t = 0; t < nrec; t++) {
            uint32_t e = ient[a0 + t], r2 = e >> 1; int pos = (int)(e & 1);
            int dd = pos ? sh : (K - sh) % K;
            rv[r2] = (uint8_t)((rv[r2] + dd) % K);
        }
        for (long long t = 0; t < nrec; t++) {
            uint32_t e = ient[a0 + t], r2 = e >> 1;
            long long p2 = r2 / G;
            uint32_t m = 0;
            for (int jj = 0; jj < G; jj++) m |= 1u << rv[p2*G + jj];
            int d = K - 1 - __builtin_popcount(m); if (d < 0) d = 0;
            pdef[p2] = (uint8_t)d;
            bad_set(p2, d > 0);
        }
        vol[f] = nv;
        if (nbadl < best) { best = nbadl; memcpy(vol_best, vol, sizeof(int) * F); }
        if (st % 20000 == 0) fprintf(stderr, "  walk step %lld bad %lld best %lld\n", st, nbadl, best);
    }
    fprintf(stderr, "  walk done: bad %lld best %lld\n", nbadl, best);
    free(bad_list); free(bad_pos);
}

int main(int argc, char **argv) {
    if (argc == 8 && !strcmp(argv[1], "walk")) {
        read_gh(argv[2]);
        K = atoi(argv[3]);
        uint64_t seed = strtoull(argv[4], NULL, 10);
        long long steps = atoll(argv[5]);
        double noise = atof(argv[6]);
        rs = seed * 2654435761ULL + 88172645463325252ULL;
        int *vol = malloc(sizeof(int) * F), *vol0 = malloc(sizeof(int) * F), *vb = malloc(sizeof(int) * F);
        for (int f = 0; f < F; f++) vol[f] = irnd(K);
        memcpy(vol0, vol, sizeof(int) * F);
        build_adj();
        insamp = calloc(NV, sizeof(int));
        for (int x = 0; x < NV; x++) insamp[x] = 1;
        records_pass(0);
        R = P * G;
        rf = malloc(sizeof(uint16_t) * (size_t)(R * 6));
        rv = malloc(sizeof(uint8_t) * (size_t)(R > 0 ? R : 1));
        pdef = malloc(sizeof(uint8_t) * (size_t)(P > 0 ? P : 1));
        records_pass(1);
        compute_rv(vol);
        build_inverse();
        walk(steps, noise, vol, vb);
        long long h2[64] = {0}, np = 0, gv = 0;
        exact_eval(vb, h2, &np, &gv);
        print_hist("EXACT_walk_best", h2, np);
        memset(h2, 0, sizeof(h2)); np = 0; gv = 0;
        exact_eval(vol0, h2, &np, &gv);
        print_hist("EXACT_random_start", h2, np);
        FILE *fo = fopen(argv[7], "w");
        if (!fo) { perror(argv[7]); return 1; }
        for (int f = 0; f < F; f++) fprintf(fo, "%d\n", vb[f]);
        fclose(fo);
        return 0;
    }
    if (argc == 10 && !strcmp(argv[1], "anneal")) {
        read_gh(argv[2]);
        K = atoi(argv[3]);
        uint64_t seed = strtoull(argv[4], NULL, 10);
        long long iters = atoll(argv[5]);
        int ns = atoi(argv[6]);
        double T0 = atof(argv[7]), T1 = atof(argv[8]);
        rs = seed * 2654435761ULL + 88172645463325252ULL;
        int *vol = malloc(sizeof(int) * F), *vol0 = malloc(sizeof(int) * F);
        for (int f = 0; f < F; f++) vol[f] = irnd(K);
        memcpy(vol0, vol, sizeof(int) * F);
        build_adj();
        insamp = calloc(NV, sizeof(int));
        if (ns <= 0 || ns >= NV) { for (int x = 0; x < NV; x++) insamp[x] = 1; }
        else {
            int *perm = malloc(sizeof(int) * NV);
            for (int x = 0; x < NV; x++) perm[x] = x;
            for (int i = 0; i < ns; i++) { int j = i + irnd(NV - i); int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp; insamp[perm[i]] = 1; }
            free(perm);
        }
        records_pass(0);
        R = P * G;
        rf = malloc(sizeof(uint16_t) * (size_t)(R * 6));
        rv = malloc(sizeof(uint8_t) * (size_t)(R > 0 ? R : 1));
        pdef = malloc(sizeof(uint8_t) * (size_t)(P > 0 ? P : 1));
        records_pass(1);
        compute_rv(vol);
        build_inverse();
        long long hist[64], total = P;
        sample_hist(hist);
        print_hist("sample_start", hist, total);
        long long nbad = anneal(iters, T0, T1, vol);
        compute_rv(vol);
        long long chk = 0; for (long long p = 0; p < P; p++) if (pdef[p]) chk++;
        sample_hist(hist);
        printf("sample_final K=%d sample_sources=%d (incremental bad %lld, fresh bad %lld)\n", K, ns <= 0 || ns >= NV ? NV : ns, nbad, chk);
        print_hist("sample_final", hist, total);
        FILE *fo = fopen(argv[9], "w");
        if (!fo) { perror(argv[9]); return 1; }
        for (int f = 0; f < F; f++) fprintf(fo, "%d\n", vol[f]);
        fclose(fo);
        long long h2[64] = {0}, np = 0, gv = 0;
        exact_eval(vol0, h2, &np, &gv);
        print_hist("EXACT_random_start", h2, np);
        memset(h2, 0, sizeof(h2)); np = 0; gv = 0;
        exact_eval(vol, h2, &np, &gv);
        print_hist("EXACT_designed", h2, np);
        printf("geodesic_count_violations %lld (expect 0)\n", gv);
        return 0;
    }
    if (argc == 5 && !strcmp(argv[1], "eval")) {
        read_gh(argv[2]);
        K = atoi(argv[3]);
        int *vol = malloc(sizeof(int) * F);
        if (!strncmp(argv[4], "random:", 7)) {
            rs = strtoull(argv[4] + 7, NULL, 10) * 2654435761ULL + 88172645463325252ULL;
            for (int f = 0; f < F; f++) vol[f] = irnd(K);
        } else {
            FILE *fi = fopen(argv[4], "r");
            if (!fi) { perror(argv[4]); return 1; }
            for (int f = 0; f < F; f++) if (fscanf(fi, "%d", &vol[f]) != 1) { fprintf(stderr, "short vol file\n"); return 1; }
            fclose(fi);
        }
        build_adj();
        long long h2[64] = {0}, np = 0, gv = 0;
        exact_eval(vol, h2, &np, &gv);
        print_hist("EXACT", h2, np);
        printf("geodesic_count_violations %lld (expect 0)\n", gv);
        return 0;
    }
    fprintf(stderr, "usage: holo anneal GH K SEED ITERS NSAMPLE T0 T1 OUT | holo eval GH K VOL|random:SEED\n");
    return 1;
}
