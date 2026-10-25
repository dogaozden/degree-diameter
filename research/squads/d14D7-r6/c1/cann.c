/* cann.c: fast annealer for the mirrored-surgery extension problem (card c1, round d14D7-r6).
 * Maximises F = (#active pairs) - cost, cost = sum over types t of max(0, cR(t) - cS(t)),
 * where cR counts base points r (R756) by type {j : B(X_j, r) = 0} and cS counts usable spread lines
 * s (not concurrent with any L_j) by type {j : d(s, L_j) = 4}.  Same definition as mirror_build.py.
 * Moves: random and best-of-M replacement of one point or one line, add pair, remove pair, compound
 * add + replace, tabu on recently removed candidates, restarts from the best state with random kicks.
 * usage: cann HEX R.txt S.txt INIT.txt OUTPREFIX SEED SECS T0 T1 CYC KICK TABU M
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define Q 11
#define KMAX 20
#define NRR 756
#define NSS 1332
#define WR 12   /* 756 bits */
#define WS 21   /* 1332 bits */

static int NP, NL, NC, NLP;
static int32_t *lp, *pl, *Sline, *candidx, *candpt, *lineconc, *plist;
static uint8_t *Xc, *isS;
static uint32_t *mark;
static uint32_t stampc = 1;
static int32_t Rid[NRR], Slist[NSS];
static uint64_t *candN, *lineN4;
static const uint64_t zeroR[WR] = {0}, zeroS[WS] = {0};
static int64_t *tabuPt, *tabuLn;   /* iteration until which the candidate is tabu */

static int xslot[KMAX], lslot[KMAX];          /* xslot: candidate index, lslot: line id, -1 = empty */
static uint32_t tR[NRR], tS[NSS];
static int cR[1 << KMAX], cS[1 << KMAX];
static int ex[NSS];
static int cost;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static inline int Bf(int i, int j) {
    const uint8_t *x = Xc + 7 * (size_t)i, *y = Xc + 7 * (size_t)j;
    int v = x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3];
    v %= Q; if (v < 0) v += Q; return v;
}

static void die(const char *m) { fprintf(stderr, "error: %s\n", m); exit(1); }

static void load_hex(const char *path) {
    FILE *f = fopen(path, "rb"); if (!f) die("hex file");
    int32_t hdr[3];
    if (fread(hdr, 4, 3, f) != 3) die("hdr");
    int q = hdr[0]; NP = hdr[1]; NL = hdr[2];
    if (q != Q) die("q");
    lp = malloc(sizeof(int32_t) * (size_t)NL * (Q + 1));
    if (fread(lp, 4, (size_t)NL * (Q + 1), f) != (size_t)NL * (Q + 1)) die("lp");
    Xc = malloc((size_t)NP * 7);
    if (fread(Xc, 1, (size_t)NP * 7, f) != (size_t)NP * 7) die("X");
    fclose(f);
    pl = malloc(sizeof(int32_t) * (size_t)NP * (Q + 1));
    int32_t *cnt = calloc(NP, sizeof(int32_t));
    for (int l = 0; l < NL; l++)
        for (int t = 0; t <= Q; t++) {
            int p = lp[l * (Q + 1) + t];
            pl[(size_t)p * (Q + 1) + cnt[p]++] = l;
        }
    for (int p = 0; p < NP; p++) if (cnt[p] != Q + 1) die("pl count");
    free(cnt);
}

static void read_ints(const char *path, int32_t *dst, int n) {
    FILE *f = fopen(path, "r"); if (!f) die("open list");
    for (int i = 0; i < n; i++) if (fscanf(f, "%d", &dst[i]) != 1) die("read list");
    fclose(f);
}

/* ---- type-count bookkeeping: cost = sum_t max(0, cR[t] - cS[t]) ---- */
static inline void incR(uint32_t t) { int d = cR[t] - cS[t]; if (d >= 0) cost++; cR[t]++; }
static inline void decR(uint32_t t) { int d = cR[t] - cS[t]; if (d >= 1) cost--; cR[t]--; }
static inline void incS(uint32_t t) { int d = cR[t] - cS[t]; if (d >= 1) cost--; cS[t]++; }
static inline void decS(uint32_t t) { int d = cR[t] - cS[t]; if (d >= 0) cost++; cS[t]--; }
static inline void sUnc(int s) { if (ex[s] == 0) decS(tS[s]); }
static inline void sCnt(int s) { if (ex[s] == 0) incS(tS[s]); }

static void setPt(int j, int nc) {
    int oc = xslot[j];
    const uint64_t *A = oc >= 0 ? candN + (size_t)oc * WR : zeroR;
    const uint64_t *Bv = nc >= 0 ? candN + (size_t)nc * WR : zeroR;
    uint32_t bit = 1u << j;
    for (int w = 0; w < WR; w++) {
        uint64_t x = A[w] ^ Bv[w];
        while (x) {
            int b = __builtin_ctzll(x); x &= x - 1; int r = w * 64 + b;
            decR(tR[r]); tR[r] ^= bit; incR(tR[r]);
        }
    }
    xslot[j] = nc;
}

static void setLn(int j, int nl) {
    int ol = lslot[j];
    int oc = ol >= 0 ? lineconc[ol] : -1, nc = nl >= 0 ? lineconc[nl] : -1;
    uint32_t bit = 1u << j;
    if (oc >= 0) { sUnc(oc); ex[oc]--; sCnt(oc); }
    if (nc >= 0) { sUnc(nc); ex[nc]++; sCnt(nc); }
    const uint64_t *A = ol >= 0 ? lineN4 + (size_t)ol * WS : zeroS;
    const uint64_t *Bv = nl >= 0 ? lineN4 + (size_t)nl * WS : zeroS;
    for (int w = 0; w < WS; w++) {
        uint64_t x = A[w] ^ Bv[w];
        while (x) {
            int b = __builtin_ctzll(x); x &= x - 1; int s = w * 64 + b;
            sUnc(s); tS[s] ^= bit; sCnt(s);
        }
    }
    lslot[j] = nl;
}

/* ---- opposition checks ---- */
static int pt_ok(int c, int skip) {
    int p = candpt[c];
    for (int i = 0; i < KMAX; i++) {
        if (i == skip || xslot[i] < 0) continue;
        int q = candpt[xslot[i]];
        if (q == p || Bf(p, q) == 0) return 0;
    }
    return 1;
}
static int ln_ok(int l, int skip) {
    stampc++;
    for (int t = 0; t < Q + 1; t++) {
        int p = lp[l * (Q + 1) + t];
        for (int u = 0; u <= Q; u++) {
            int m = pl[(size_t)p * (Q + 1) + u];
            for (int v = 0; v <= Q; v++) mark[lp[m * (Q + 1) + v]] = stampc;
        }
    }
    for (int i = 0; i < KMAX; i++) {
        if (i == skip || lslot[i] < 0) continue;
        int m = lslot[i];
        if (m == l) return 0;
        for (int v = 0; v <= Q; v++) if (mark[lp[m * (Q + 1) + v]] == stampc) return 0;
    }
    return 1;
}

/* ---- undo log ---- */
typedef struct { int type, slot, old; } U;
static U ulog[64]; static int nlog;
static void doPt(int j, int nc) { ulog[nlog].type = 0; ulog[nlog].slot = j; ulog[nlog].old = xslot[j]; nlog++; setPt(j, nc); }
static void doLn(int j, int nl) { ulog[nlog].type = 1; ulog[nlog].slot = j; ulog[nlog].old = lslot[j]; nlog++; setLn(j, nl); }
static void undo(void) {
    while (nlog) {
        U u = ulog[--nlog];
        if (u.type == 0) setPt(u.slot, u.old); else setLn(u.slot, u.old);
    }
}

static int nact(void) { int k = 0; for (int j = 0; j < KMAX; j++) if (xslot[j] >= 0 && lslot[j] >= 0) k++; return k; }
static int ptused(int c) { for (int i = 0; i < KMAX; i++) if (xslot[i] == c) return 1; return 0; }
static int lnused(int l) { for (int i = 0; i < KMAX; i++) if (lslot[i] == l) return 1; return 0; }

/* random valid point candidate for slot skip (not tabu, not used) */
static int rand_pt(int skip, int tabu_on, uint64_t it) {
    for (int tries = 0; tries < 200; tries++) {
        int c = rndint(NC);
        if (ptused(c)) continue;
        if (tabu_on && tabuPt[c] > (int64_t)it) continue;
        if (pt_ok(c, skip)) return c;
    }
    return -1;
}
static int rand_ln(int skip, int tabu_on, uint64_t it) {
    for (int tries = 0; tries < 200; tries++) {
        int l = plist[rndint(NLP)];
        if (lnused(l)) continue;
        if (tabu_on && tabuLn[l] > (int64_t)it) continue;
        if (ln_ok(l, skip)) return l;
    }
    return -1;
}

/* best-of-M replacement of point in slot j: evaluate delta cost for M random valid candidates */
static int best_pt(int j, int M, uint64_t it, int tabu_on) {
    int bestc = -1, bestd = 1 << 30, nties = 0, oc = xslot[j];
    for (int s = 0; s < M; s++) {
        int c = rndint(NC);
        if (c == oc || ptused(c)) continue;
        if (tabu_on && tabuPt[c] > (int64_t)it) continue;
        int before = cost; setPt(j, c); int d = cost - before; setPt(j, oc);
        if (d > bestd) continue;
        if (!pt_ok(c, j)) continue;
        if (d < bestd) { bestd = d; bestc = c; nties = 1; }
        else if (d == bestd && rndint(++nties) == 0) bestc = c;
    }
    return bestc;
}
static int best_ln(int j, int M, uint64_t it, int tabu_on) {
    int bestl = -1, bestd = 1 << 30, nties = 0, ol = lslot[j];
    for (int s = 0; s < M; s++) {
        int l = plist[rndint(NLP)];
        if (l == ol || lnused(l)) continue;
        if (tabu_on && tabuLn[l] > (int64_t)it) continue;
        int before = cost; setLn(j, l); int d = cost - before; setLn(j, ol);
        if (d > bestd) continue;
        if (!ln_ok(l, j)) continue;
        if (d < bestd) { bestd = d; bestl = l; nties = 1; }
        else if (d == bestd && rndint(++nties) == 0) bestl = l;
    }
    return bestl;
}

static int recompute_cost(void) {
    static int tcR[1 << KMAX], tcS[1 << KMAX];
    memset(tcR, 0, sizeof(tcR)); memset(tcS, 0, sizeof(tcS));
    for (int r = 0; r < NRR; r++) tcR[tR[r]]++;
    for (int s = 0; s < NSS; s++) if (ex[s] == 0) tcS[tS[s]]++;
    int c = 0;
    for (int t = 0; t < (1 << KMAX); t++) if (tcR[t] > tcS[t]) c += tcR[t] - tcS[t];
    return c;
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

static void save_state(const char *path, int F, const int *bx, const int *bl) {
    FILE *f = fopen(path, "w"); if (!f) return;
    int k = 0; for (int j = 0; j < KMAX; j++) if (bx[j] >= 0 && bl[j] >= 0) k++;
    fprintf(f, "F %d k %d\nX", F, k);
    for (int j = 0; j < KMAX; j++) if (bx[j] >= 0 && bl[j] >= 0) fprintf(f, " %d", candpt[bx[j]]);
    fprintf(f, "\nL");
    for (int j = 0; j < KMAX; j++) if (bx[j] >= 0 && bl[j] >= 0) fprintf(f, " %d", bl[j]);
    fprintf(f, "\n");
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 15) { fprintf(stderr, "usage: cann HEX R.txt S.txt INIT.txt OUTPREFIX SEED SECS T0 T1 CYC KICK TABU M ADDK\n"); return 1; }
    const char *hexp = argv[1], *Rf = argv[2], *Sf = argv[3], *initf = argv[4], *outp = argv[5];
    uint64_t seed = strtoull(argv[6], 0, 10); double secs = atof(argv[7]);
    double T0 = atof(argv[8]), T1 = atof(argv[9]); long CYC = atol(argv[10]); int KICK = atoi(argv[11]);
    int TABU = atoi(argv[12]); int M = atoi(argv[13]); int ADDK = atoi(argv[14]);
    int FIXK = argc > 15 ? atoi(argv[15]) : 0;
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd64();
    double t0 = now();
    load_hex(hexp);
    read_ints(Rf, Rid, NRR); read_ints(Sf, Slist, NSS);
    isS = calloc(NL, 1); Sline = malloc(4 * (size_t)NP);
    for (int p = 0; p < NP; p++) Sline[p] = -1;
    for (int j = 0; j < NSS; j++) {
        int s = Slist[j]; isS[s] = 1;
        for (int t = 0; t <= Q; t++) { int p = lp[s * (Q + 1) + t]; if (Sline[p] >= 0) die("S not disjoint"); Sline[p] = j; }
    }
    /* base-point collinearity: candidates are points not collinear with R (and not in R) */
    uint8_t *colR = calloc(NP, 1);
    for (int r = 0; r < NRR; r++) {
        int p = Rid[r];
        for (int u = 0; u <= Q; u++) { int m = pl[(size_t)p * (Q + 1) + u]; for (int v = 0; v <= Q; v++) colR[lp[m * (Q + 1) + v]] = 1; }
    }
    candidx = malloc(4 * (size_t)NP); candpt = malloc(4 * (size_t)NP); NC = 0;
    for (int p = 0; p < NP; p++) { if (!colR[p]) { candidx[p] = NC; candpt[NC++] = p; } else candidx[p] = -1; }
    /* candidate R-neighbourhoods: bit r set iff B(c, R[r]) == 0 */
    candN = calloc((size_t)NC * WR, sizeof(uint64_t));
    for (int c = 0; c < NC; c++)
        for (int r = 0; r < NRR; r++)
            if (Bf(candpt[c], Rid[r]) == 0) candN[(size_t)c * WR + r / 64] |= 1ULL << (r % 64);
    /* plist: non-S lines; lineN4: S-lines at distance 4 (bitset over S index); lineconc: the unique S-line meeting l */
    plist = malloc(4 * (size_t)NL); NLP = 0;
    lineN4 = calloc((size_t)NL * WS, sizeof(uint64_t));
    lineconc = malloc(4 * (size_t)NL);
    int badconc = 0;
    for (int l = 0; l < NL; l++) {
        lineconc[l] = -1; if (isS[l]) continue;
        plist[NLP++] = l;
        int conc = -1, nconc = 0;
        for (int t = 0; t <= Q; t++) { int p = lp[l * (Q + 1) + t]; if (Sline[p] >= 0) { conc = Sline[p]; nconc++; } }
        if (nconc != 1) badconc++;
        uint64_t *row = lineN4 + (size_t)l * WS;
        for (int t = 0; t <= Q; t++) {
            int p = lp[l * (Q + 1) + t];
            for (int u = 0; u <= Q; u++) {
                int m = pl[(size_t)p * (Q + 1) + u];
                for (int v = 0; v <= Q; v++) { int s = Sline[lp[m * (Q + 1) + v]]; if (s >= 0) row[s / 64] |= 1ULL << (s % 64); }
            }
        }
        if (conc >= 0) row[conc / 64] &= ~(1ULL << (conc % 64));
        lineconc[l] = conc;
    }
    mark = calloc(NP, sizeof(uint32_t));
    tabuPt = calloc(NC, sizeof(int64_t)); tabuLn = calloc(NL, sizeof(int64_t));
    fprintf(stderr, "loaded NP %d NL %d NC %d NLP %d badconc %d [%.1fs]\n", NP, NL, NC, NLP, badconc, now() - t0);

    /* initial state */
    for (int j = 0; j < KMAX; j++) { xslot[j] = -1; lslot[j] = -1; }
    cR[0] = NRR; cS[0] = NSS; cost = 0;
    FILE *fi = fopen(initf, "r"); if (!fi) die("init");
    int k0; if (fscanf(fi, "%d", &k0) != 1) die("init k");
    int32_t X0[KMAX], L0[KMAX];
    for (int i = 0; i < k0; i++) if (fscanf(fi, "%d", &X0[i]) != 1) die("init X");
    for (int i = 0; i < k0; i++) if (fscanf(fi, "%d", &L0[i]) != 1) die("init L");
    fclose(fi);
    for (int i = 0; i < k0; i++) { if (candidx[X0[i]] < 0) die("init point not a candidate"); setPt(i, candidx[X0[i]]); setLn(i, L0[i]); }
    if (recompute_cost() != cost) die("cost bookkeeping mismatch at init");
    int F = nact() - cost;
    fprintf(stderr, "init k %d cost %d F %d\n", nact(), cost, F);
    /* random pairs to add at start */
    for (int a = 0; a < ADDK; a++) {
        int j = -1; for (int i = 0; i < KMAX; i++) if (xslot[i] < 0 && lslot[i] < 0) { j = i; break; }
        if (j < 0) break;
        int c = rand_pt(-1, 0, 0); if (c < 0) break;
        setPt(j, c);
        int l = rand_ln(-1, 0, 0); if (l < 0) { setPt(j, -1); break; }
        setLn(j, l);
    }
    F = nact() - cost;

    int bestF = -1000, bx[KMAX], bl[KMAX];
    for (int j = 0; j < KMAX; j++) { bx[j] = xslot[j]; bl[j] = lslot[j]; }
    bestF = F;
    char path[1024];
    snprintf(path, sizeof path, "%s_best.txt", outp); save_state(path, bestF, bx, bl);
    fprintf(stderr, "start F %d k %d cost %d [%.1fs]\n", F, nact(), cost, now() - t0);

    double tstart = now(); uint64_t it = 0; uint64_t lastimp = 0; long cycle_it = 0;
    double T = T0; long nprop[8] = {0}, nacc[8] = {0};
    double lastlog = now();
    while (now() - tstart < secs) {
        it++; cycle_it++;
        if (cycle_it >= CYC) {  /* restart: back to best, kick, reheat */
            for (int j = 0; j < KMAX; j++) { if (xslot[j] != bx[j] || lslot[j] != bl[j]) { setPt(j, bx[j]); setLn(j, bl[j]); } }
            for (int kk = 0; kk < KICK; kk++) {
                int j = rndint(KMAX); if (xslot[j] < 0 || lslot[j] < 0) continue;
                int c = rand_pt(j, 0, it); if (c >= 0) setPt(j, c);
                int l = rand_ln(j, 0, it); if (l >= 0) setLn(j, l);
            }
            cycle_it = 0; T = T0;
            F = nact() - cost;
        }
        T = T0 * pow(T1 / T0, (double)cycle_it / (double)CYC);
        nlog = 0;
        int Fbefore = nact() - cost;
        /* choose slots */
        int act[KMAX], na = 0; int freej = -1;
        for (int j = 0; j < KMAX; j++) { if (xslot[j] >= 0 && lslot[j] >= 0) act[na++] = j; else if (xslot[j] < 0 && lslot[j] < 0 && freej < 0) freej = j; }
        double u = rnd01(); int mv;
        if (na == 0) mv = 4;
        else if (FIXK) { if (u < 0.25) mv = 0; else if (u < 0.5) mv = 1; else if (u < 0.7) mv = 2; else if (u < 0.9) mv = 3; else mv = 7; }
        else if (u < 0.22) mv = 0;      /* best-of-M point replacement */
        else if (u < 0.44) mv = 1;      /* best-of-M line replacement */
        else if (u < 0.58) mv = 2;      /* random point replacement */
        else if (u < 0.72) mv = 3;      /* random line replacement */
        else if (u < 0.84) mv = 4;      /* add pair */
        else if (u < 0.92) mv = 5;      /* remove pair */
        else mv = 6;                    /* compound: add pair + best point replacement elsewhere */
        nprop[mv]++;
        int ok = 1;
        if (mv == 0) {
            int j = act[rndint(na)], c = best_pt(j, M, it, 1);
            if (c < 0) ok = 0; else doPt(j, c);
        } else if (mv == 1) {
            int j = act[rndint(na)], l = best_ln(j, M, it, 1);
            if (l < 0) ok = 0; else doLn(j, l);
        } else if (mv == 2) {
            int j = act[rndint(na)], c = rand_pt(j, 1, it);
            if (c < 0) ok = 0; else doPt(j, c);
        } else if (mv == 3) {
            int j = act[rndint(na)], l = rand_ln(j, 1, it);
            if (l < 0) ok = 0; else doLn(j, l);
        } else if (mv == 4) {
            if (freej < 0 || na >= KMAX) ok = 0;
            else {
                int c = rand_pt(-1, 1, it), l = (c >= 0) ? rand_ln(-1, 1, it) : -1;
                if (c < 0 || l < 0) ok = 0; else { doPt(freej, c); doLn(freej, l); }
            }
        } else if (mv == 5) {
            int j = act[rndint(na)];
            tabuPt[xslot[j]] = (int64_t)it + TABU; tabuLn[lslot[j]] = (int64_t)it + TABU;
            doPt(j, -1); doLn(j, -1);
        } else if (mv == 7) {  /* fixed-k: replace point and line of one slot at random */
            int j = act[rndint(na)], c = rand_pt(j, 1, it), l = (c >= 0) ? rand_ln(j, 1, it) : -1;
            if (c < 0 || l < 0) ok = 0; else { doPt(j, c); doLn(j, l); }
        } else {  /* compound */
            if (freej < 0) ok = 0;
            else {
                int c = rand_pt(-1, 1, it), l = (c >= 0) ? rand_ln(-1, 1, it) : -1;
                if (c < 0 || l < 0) ok = 0;
                else {
                    doPt(freej, c); doLn(freej, l);
                    int j = act[rndint(na)];
                    int c2 = best_pt(j, M / 4, it, 1);
                    if (c2 >= 0) doPt(j, c2);
                }
            }
        }
        if (ok) {
            int Fafter = nact() - cost;
            int dF = Fafter - Fbefore;
            if (dF >= 0 || rnd01() < exp(dF / T)) {
                nacc[mv]++;
                F = Fafter;
                if (F > bestF) {
                    bestF = F; for (int j = 0; j < KMAX; j++) { bx[j] = xslot[j]; bl[j] = lslot[j]; }
                    snprintf(path, sizeof path, "%s_best.txt", outp); save_state(path, bestF, bx, bl);
                    lastimp = it;
                    fprintf(stderr, "NEW BEST F %d (k %d cost %d) it %llu [%.1fs]\n", F, nact(), cost, (unsigned long long)it, now() - t0);
                    if (cost == 0 && nact() >= 12) {
                        snprintf(path, sizeof path, "%s_F%d.txt", outp, F); save_state(path, bestF, bx, bl);
                    }
                }
            } else {
                undo();
            }
        } else {
            nlog = 0;
        }
        if (now() - lastlog > 20.0) {
            lastlog = now();
            fprintf(stderr, "it %llu T %.3f F %d k %d cost %d best %d | acc:", (unsigned long long)it, T, F, nact(), cost, bestF);
            for (int m = 0; m < 8; m++) fprintf(stderr, " %d:%ld/%ld", m, nacc[m], nprop[m]);
            fprintf(stderr, " [%.0fs]\n", now() - t0);
        }
        /* sanity: incremental cost equals recomputed cost occasionally */
        if ((it & ((1 << 20) - 1)) == 0) {
            int rc = recompute_cost();
            if (rc != cost) { fprintf(stderr, "MISMATCH cost %d vs %d\n", cost, rc); return 2; }
        }
    }
    if (recompute_cost() != cost) { fprintf(stderr, "MISMATCH at end\n"); return 2; }
    fprintf(stderr, "done: iterations %llu, best F %d, last improvement at it %llu\n", (unsigned long long)it, bestF, (unsigned long long)lastimp);
    printf("best F %d\n", bestF);
    return 0;
}
