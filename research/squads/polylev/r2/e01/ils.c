/* e01: local search on partial spreads of totally singular lines of Q(6,11).
 *
 * State: OWNER[idx] = slot of the line covering the point (or -1); slot s holds 12 point indices SP[s][*].
 * Point index idx(v) = OFF[f] + Horner(v_{f+1..6}) for the normalised v (first nonzero entry 1, index f); range M.
 * Move: pick a random uncovered point p; among the lines through p (each has conflict set = distinct lines
 * already covering its points) take one with the fewest conflicts c <= CMAX (random tie break); remove the
 * conflicting lines, add the line, then refill the freed uncovered points greedily with free lines.
 * Delta = 1 - c + fills; accept if Delta >= 0, otherwise undo through the journal.
 *
 * Usage: ils HEXBIN INIT.txt OUT.txt SEED TIMELIMIT_SEC [CMAX]
 * INIT.txt: one line of 12 hexagon point ids per line (hex_q11.bin row ids). OUT.txt: same format.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define Q 11
#define D 7
#define NMAX 177156
#define M 1948717
#define LN 12
#define MAXSLOT 6000000
#define JMAX 4000000

static int OFF[D];
static uint8_t NRM[NMAX][D];
static int32_t IDXP[NMAX];
static int32_t PIDOF[M];
static int32_t OWNER[M];
static int32_t (*SP)[LN];
static int nslot = 0;
static int32_t HK[D][NMAX];
static int HN[D];
static const int INV[Q] = {0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10};
static uint64_t rs = 88172645463325252ULL;
static int32_t JI[JMAX], JO[JMAX];
static int jn = 0;
static int32_t freeY[2000];
static int32_t tmpF[16 * LN];

static inline uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static inline int idx_of(const int *v) {
    int f = 0;
    while (v[f] == 0) f++;
    int c = INV[v[f]];
    int rest = 0;
    for (int j = f + 1; j < D; j++) rest = rest * Q + (v[j] * c % Q);
    return OFF[f] + rest;
}

static inline int bform(const uint8_t *x, const uint8_t *y) {
    int s = x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3];
    s %= Q;
    if (s < 0) s += Q;
    return s;
}

static inline int pivot(int pid) {
    int k = 0;
    while (NRM[pid][k] == 0) k++;
    return k;
}

/* the 12 point indices of the line through pid p and the hyperplane point y (y_k0 = 0, b(p,y)=0) */
static inline void build_line(int p, int y, int32_t *out) {
    out[0] = IDXP[p];
    int v[D];
    for (int t = 0; t < Q; t++) {
        for (int j = 0; j < D; j++) v[j] = (NRM[y][j] + t * NRM[p][j]) % Q;
        out[1 + t] = idx_of(v);
    }
}

static inline void jset(int32_t idx, int32_t val) {
    JI[jn] = idx;
    JO[jn] = OWNER[idx];
    jn++;
    OWNER[idx] = val;
}

static void add_line(const int32_t *L) {
    int s = nslot++;
    if (s >= MAXSLOT) {
        fprintf(stderr, "slot table full\n");
        exit(1);
    }
    for (int i = 0; i < LN; i++) SP[s][i] = L[i];
    for (int i = 0; i < LN; i++) jset(L[i], s);
}

static void write_solution(const char *path, int *count_out) {
    char *seen = calloc(nslot + 1, 1);
    FILE *o = fopen(path, "w");
    int K = 0;
    for (int idx = 0; idx < M; idx++) {
        int s = OWNER[idx];
        if (s < 0 || seen[s]) continue;
        seen[s] = 1;
        K++;
        for (int i = 0; i < LN; i++) fprintf(o, "%d%c", PIDOF[SP[s][i]], i == LN - 1 ? '\n' : ' ');
    }
    fclose(o);
    free(seen);
    *count_out = K;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: ils HEXBIN INIT OUT SEED TIMELIMIT [CMAX]\n");
        return 1;
    }
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    double tlim = atof(argv[5]);
    int CMAX = argc > 6 ? atoi(argv[6]) : 2;
    time_t w0 = time(NULL);

    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("hex"); return 1; }
    int hdr[3];
    if (fread(hdr, 4, 3, f) != 3) return 1;
    int N = hdr[1], L = hdr[2];
    if (hdr[0] != Q || N > NMAX) { fprintf(stderr, "bad hex\n"); return 1; }
    fseek(f, 12 + 4L * L * (Q + 1), SEEK_SET);
    uint8_t *raw = malloc((size_t)N * D);
    if (fread(raw, 1, (size_t)N * D, f) != (size_t)N * D) return 1;
    fclose(f);

    OFF[0] = 0;
    {
        long acc = 0;
        for (int g = 0; g < D; g++) {
            OFF[g] = (int)acc;
            long sz = 1;
            for (int e = 0; e < D - 1 - g; e++) sz *= Q;
            acc += sz;
        }
        if (acc != M) { fprintf(stderr, "M mismatch %ld\n", acc); return 1; }
    }
    for (int i = 0; i < M; i++) { OWNER[i] = -1; PIDOF[i] = -1; }
    for (int i = 0; i < N; i++) {
        int v[D];
        for (int j = 0; j < D; j++) v[j] = raw[i * D + j];
        int f0 = 0;
        while (v[f0] == 0) f0++;
        int c = INV[v[f0]];
        for (int j = 0; j < D; j++) NRM[i][j] = (uint8_t)(v[j] * c % Q);
        int qq = (NRM[i][0] * NRM[i][4] + NRM[i][1] * NRM[i][5] + NRM[i][2] * NRM[i][6] - NRM[i][3] * NRM[i][3]) % Q;
        if (qq < 0) qq += Q;
        if (qq != 0) { fprintf(stderr, "point %d not singular\n", i); return 1; }
        int vv[D];
        for (int j = 0; j < D; j++) vv[j] = NRM[i][j];
        IDXP[i] = idx_of(vv);
        if (PIDOF[IDXP[i]] != -1) { fprintf(stderr, "dup point\n"); return 1; }
        PIDOF[IDXP[i]] = i;
    }
    free(raw);
    for (int k = 0; k < D; k++) {
        HN[k] = 0;
        for (int i = 0; i < N; i++)
            if (NRM[i][k] == 0) HK[k][HN[k]++] = i;
    }
    SP = malloc(sizeof(*SP) * (size_t)MAXSLOT);

    /* read initial solution */
    {
        FILE *in = fopen(argv[2], "r");
        if (!in) { perror("init"); return 1; }
        int v[LN];
        while (1) {
            int ok = 1;
            for (int i = 0; i < LN; i++)
                if (fscanf(in, "%d", &v[i]) != 1) { ok = 0; break; }
            if (!ok) break;
            int32_t L12[LN];
            for (int i = 0; i < LN; i++) {
                if (v[i] < 0 || v[i] >= N) { fprintf(stderr, "bad id\n"); return 1; }
                L12[i] = IDXP[v[i]];
                if (OWNER[L12[i]] != -1) { fprintf(stderr, "init not disjoint\n"); return 1; }
            }
            int s = nslot++;
            for (int i = 0; i < LN; i++) { SP[s][i] = L12[i]; OWNER[L12[i]] = s; }
        }
        fclose(in);
    }
    int K = nslot;
    fprintf(stderr, "init: %d lines\n", K);
    int uncovered_init = 0;
    for (int i = 0; i < N; i++) if (OWNER[IDXP[i]] < 0) uncovered_init++;
    fprintf(stderr, "init uncovered points: %d\n", uncovered_init);

    long iter = 0, acc_moves = 0, c_hist[4] = {0, 0, 0, 0};
    int lastK = K;
    time_t lastout = time(NULL);
    int32_t Lcur[LN], Lfill[LN];
    int32_t Fbuf[16 * LN * 4];
    while (1) {
        iter++;
        if ((iter & 63) == 0) {
            double el = difftime(time(NULL), w0);
            if (el > tlim) break;
            if (difftime(time(NULL), lastout) > 120) {
                int Kc;
                write_solution(argv[3], &Kc);
                fprintf(stderr, "t=%.0fs iter=%ld K=%d (check %d) accepted=%ld\n", el, iter, K, Kc, acc_moves);
                lastout = time(NULL);
            }
        }
        /* random uncovered point */
        int p;
        do { p = (int)(rnd() % N); } while (OWNER[IDXP[p]] >= 0);
        int k0 = pivot(p);
        int bestc = 99, bestcnt = 0, bestY = -1;
        int32_t bestS[LN];
        for (int a = 0; a < HN[k0]; a++) {
            int y = HK[k0][a];
            if (bform(NRM[p], NRM[y]) != 0) continue;
            build_line(p, y, Lcur);
            int cs[LN], cn = 0;
            int over = 0;
            for (int i = 0; i < LN && !over; i++) {
                int o = OWNER[Lcur[i]];
                if (o < 0) continue;
                int dup = 0;
                for (int j = 0; j < cn; j++) if (cs[j] == o) { dup = 1; break; }
                if (!dup) {
                    if (cn == CMAX) over = 1;
                    else cs[cn++] = o;
                }
            }
            if (over) continue;
            if (cn < bestc) {
                bestc = cn; bestcnt = 1; bestY = y;
                for (int j = 0; j < cn; j++) bestS[j] = cs[j];
            } else if (cn == bestc) {
                bestcnt++;
                if (rnd() % (uint64_t)bestcnt == 0) {
                    bestY = y;
                    for (int j = 0; j < cn; j++) bestS[j] = cs[j];
                }
            }
        }
        if (bestY < 0 || bestc == 0) { if (bestc == 0 && bestY >= 0) { /* free line: just add */
                build_line(p, bestY, Lcur); jn = 0; add_line(Lcur); K += 1; acc_moves++; }
            continue; }
        c_hist[bestc]++;
        jn = 0;
        int nF = 0;
        int32_t *F = Fbuf;
        /* remove conflicting lines */
        for (int j = 0; j < bestc; j++) {
            int s = bestS[j];
            for (int i = 0; i < LN; i++) {
                int32_t idx = SP[s][i];
                F[nF++] = idx;
                jset(idx, -1);
            }
        }
        build_line(p, bestY, Lcur);
        add_line(Lcur);
        /* refill freed points, random order */
        for (int i = nF - 1; i > 0; i--) {
            int j = (int)(rnd() % (uint64_t)(i + 1));
            int32_t t = F[i]; F[i] = F[j]; F[j] = t;
        }
        int fills = 0;
        for (int i = 0; i < nF; i++) {
            int32_t fi = F[i];
            if (OWNER[fi] >= 0) continue;
            int pf = PIDOF[fi];
            int kf = pivot(pf);
            int nfree = 0;
            for (int a = 0; a < HN[kf]; a++) {
                int y = HK[kf][a];
                if (bform(NRM[pf], NRM[y]) != 0) continue;
                build_line(pf, y, Lfill);
                int ok = 1;
                for (int t = 0; t < LN; t++) if (OWNER[Lfill[t]] >= 0) { ok = 0; break; }
                if (ok) { if (nfree < 2000) freeY[nfree++] = y; }
            }
            if (nfree == 0) continue;
            int y = freeY[rnd() % (uint64_t)nfree];
            build_line(pf, y, Lfill);
            add_line(Lfill);
            fills++;
        }
        int delta = 1 - bestc + fills;
        if (delta >= 0) {
            K += delta;
            acc_moves++;
        } else {
            for (int j = jn - 1; j >= 0; j--) OWNER[JI[j]] = JO[j];
        }
        if (nslot > MAXSLOT - 100000) {
            fprintf(stderr, "slot budget nearly exhausted, stopping\n");
            break;
        }
        if (K > lastK) { lastK = K; }
    }
    int Kc;
    write_solution(argv[3], &Kc);
    fprintf(stderr, "final: tracked K=%d, recount=%d, iters=%ld accepted=%ld c-hist %ld %ld %ld; slots %d\n", K, Kc,
            iter, acc_moves, c_hist[0], c_hist[1], c_hist[2], nslot);
    printf("%d\n", Kc);
    return 0;
}
