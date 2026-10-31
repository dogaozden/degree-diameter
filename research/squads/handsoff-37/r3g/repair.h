/* repair.h (r3g): SA and breakout repair, extracted from grow.c; needs lift2.c included first */
/* SA from the current state (it, NI) with lift2 moves; returns best cost, best state in bIt/bNI */
static int sa_repair(double secs, double T0, double T1, long iters, Item *bIt, int *bNI, int *bcost) {
    double t0 = now();
    rebuild();
    int best = cost_full();
    memcpy(bIt, it, sizeof(Item) * NI); *bNI = NI;
    Item sv[MAXI]; int svNI;
    double lt0 = log(T0), lt1 = log(T1);
    long total = 0, rounds = 0;
    while (best > 0 && now() - t0 < secs) {
        rounds++;
        NI = *bNI; memcpy(it, bIt, sizeof(Item) * NI); rebuild();
        int cur = best;
        for (long s = 0; s < iters && now() - t0 < secs; s++) {
            double T = exp(lt0 + (lt1 - lt0) * (double)s / (double)iters);
            svNI = NI; memcpy(sv, it, sizeof(Item) * NI);
            if (!apply_move()) { NI = svNI; memcpy(it, sv, sizeof(Item) * NI); continue; }
            total++;
            rebuild();
            int nc = cost_full();
            int d = nc - cur;
            if (d <= 0 || rndu() < exp(-d / T)) {
                cur = nc;
                if (cur < best) { best = cur; *bNI = NI; memcpy(bIt, it, sizeof(Item) * NI); }
            } else { NI = svNI; memcpy(it, sv, sizeof(Item) * NI); rebuild(); }
        }
    }
    *bcost = best;
    printf("  sa: moves=%ld rounds=%ld best=%d time=%.0f\n", total, rounds, best, now() - t0);
    fflush(stdout);
    return best;
}


/* ---- breakout (clause weighting) repair: weights W on uncovered same-side pairs, bumped when stuck ---- */
static int W[MAXM][MAXM];
static void cover6(uint64_t Cv[MAXM][2]) {
    static uint64_t Bw[MAXM][2], H2[MAXM][2];
    for (int j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (int w2 = 0; w2 < 2; w2++) { uint64_t x = adj[j][w2];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w2 * 64 + tt; r0 |= adj[kk][0]; r1 |= adj[kk][1]; } }
        Bw[j][0] = r0; Bw[j][1] = r1;
    }
    for (int j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (int w2 = 0; w2 < 2; w2++) { uint64_t x = Bw[j][w2];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w2 * 64 + tt; r0 |= Bw[kk][0]; r1 |= Bw[kk][1]; } }
        H2[j][0] = r0; H2[j][1] = r1;
    }
    for (int i = 0; i < m; i++) {
        uint64_t r0 = 0, r1 = 0;
        for (int w2 = 0; w2 < 2; w2++) { uint64_t x = Bw[i][w2];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w2 * 64 + tt; r0 |= H2[kk][0]; r1 |= H2[kk][1]; } }
        Cv[i][0] = r0; Cv[i][1] = r1;
    }
}
static int wcost(int *real, int bump) {
    static uint64_t Cv[MAXM][2];
    cover6(Cv);
    int wsum = 0, rsum = 0;
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
        int cov = (Cv[i][j >> 6] >> (j & 63)) & 1;
        if (!cov) { wsum += W[i][j]; rsum++; if (bump) { W[i][j]++; W[j][i] = W[i][j]; } }
    }
    *real = rsum;
    return wsum;
}
static void setW1(void) { for (int i = 0; i < MAXM; i++) for (int j = 0; j < MAXM; j++) W[i][j] = 1; }
/* breakout repair from current state; K = non-improving proposals before a weight bump; returns best real cost */
static int breakout_run(double secs, long K, Item *bIt, int *bNI, int *bcost) {
    double t0 = now();
    setW1();
    rebuild();
    int rc, wc = wcost(&rc, 0);
    int best = rc; memcpy(bIt, it, sizeof(Item) * NI); *bNI = NI;
    Item sv[MAXI]; int svNI; long stuck = 0, props = 0, bumps = 0;
    while (best > 0 && now() - t0 < secs) {
        svNI = NI; memcpy(sv, it, sizeof(Item) * NI);
        props++;
        if (!apply_move()) { NI = svNI; memcpy(it, sv, sizeof(Item) * NI); continue; }
        rebuild();
        int nrc, nwc = wcost(&nrc, 0);
        if (nwc <= wc) {
            wc = nwc; rc = nrc;
            if (rc < best) { best = rc; *bNI = NI; memcpy(bIt, it, sizeof(Item) * NI); }
            stuck = 0;
        } else {
            NI = svNI; memcpy(it, sv, sizeof(Item) * NI); rebuild();
            if (++stuck >= K) {
                /* bump weights of the currently uncovered pairs */
                wcost(&rc, 1); bumps++;
                wc = wcost(&rc, 0);
                stuck = 0;
            }
        }
    }
    *bcost = best;
    printf("  breakout: props=%ld bumps=%ld best=%d time=%.0f\n", props, bumps, best, now() - t0);
    fflush(stdout);
    return best;
}

