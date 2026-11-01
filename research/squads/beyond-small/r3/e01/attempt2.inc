static int NLS = 40, NSAMP = 30000;
static inline double objf(const uint64_t *covO, const uint64_t *hitO, const int *L, double wH) {
    int uA = 0, uH = 0;
    for (int w = 0; w < W; w++) uA += __builtin_popcountll(~(covO[w] | ballB[L[0]][w] | ballB[L[1]][w] | ballB[L[2]][w] | ballB[L[3]][w]));
    for (int w = 0; w < HW; w++) uH += __builtin_popcountll(hm[w] & ~(hitO[w] | S[L[0]][w] | S[L[1]][w] | S[L[2]][w] | S[L[3]][w]));
    return uA / (double)H + wH * uH / (double)(NHB > 0 ? NHB : 1);
}
/* joint greedy (3 lines) then min-conflict local search over 4 lines (sampled candidates) */
static int attempt(int K, double noise, double wH, int *outN, int *outSz) {
    uint64_t covA[W], hit[HW], KU[12];
    memset(covA, 0, sizeof covA); memset(hit, 0, sizeof hit); memset(KU, 0, sizeof KU);
    int chosen[17], nc = 0;
    for (int step = 0; step < 3; step++) {
        int best = -1; double bs = -1e18; long valid = 0;
        for (long tries = 0; valid < K && tries < 60L * K; tries++) {
            int i = (int)(rnd64() % (unsigned long long)NL); int *L = lines[i];
            if (!freeline(L, KU)) continue;
            valid++;
            double sc = gainA(covA, L) / (double)H + wH * gainH(hit, L) / (double)(NHB > 0 ? NHB : 1) + noise * urand();
            if (sc > bs) { bs = sc; best = i; }
        }
        if (best < 0) { stat_fail[0]++; return 0; }
        addl(lines[best], chosen, &nc, KU, covA, hit);
    }
    /* four line indices: the 3 greedy lines are chosen[0..11] as vertex lists; recover them as line-vertex groups */
    int ln[4][4];
    for (int q = 0; q < 3; q++) for (int k = 0; k < 4; k++) ln[q][k] = chosen[4 * q + k];
    /* local search: position p gets the best sampled replacement (ties random) */
    double cur = -1;
    for (int it = 0; it < NLS; it++) {
        int p = (it < 3) ? 3 : (it % 4);  /* first fill position 3 from the samples, then cycle */
        uint64_t cO[W], hO[HW], KO[12]; memset(cO, 0, sizeof cO); memset(hO, 0, sizeof hO); memset(KO, 0, sizeof KO);
        int oth[4][4], no = 0;
        for (int q = 0; q < 4; q++) if (q != p) { memcpy(oth[no], ln[q], sizeof(int) * 4); no++; }
        for (int q = 0; q < 3; q++) for (int k = 0; k < 4; k++) { int v = oth[q][k]; setb(KO, keyof(v));
            for (int w = 0; w < W; w++) cO[w] |= ballB[v][w]; for (int w = 0; w < HW; w++) hO[w] |= S[v][w]; }
        double bo = 1e18; int bi = -1, nt = 0;
        for (int s = 0; s < NSAMP; s++) {
            int i = (int)(rnd64() % (unsigned long long)NL); int *L = lines[i];
            if (!freeline(L, KO)) continue;
            double o = objf(cO, hO, L, wH);
            if (o < bo - 1e-12) { bo = o; bi = i; nt = 1; }
            else if (fabs(o - bo) <= 1e-12 && (rnd64() % (unsigned long long)(++nt)) == 0) bi = i;
        }
        if (bi < 0) continue;
        memcpy(ln[p], lines[bi], sizeof(int) * 4); cur = bo;
        if (bo <= 0.0) break;
    }
    /* verify final 4 lines: key-distinct, free, complete */
    uint64_t covF[W], hitF[HW], KF[12]; memset(covF, 0, sizeof covF); memset(hitF, 0, sizeof hitF); memset(KF, 0, sizeof KF);
    int fin[16], nf = 0;
    for (int q = 0; q < 4; q++) for (int k = 0; k < 4; k++) {
        int v = ln[q][k];
        if (used[v] || bitq(KF, keyof(v))) { stat_fail[0]++; return 0; }
        setb(KF, keyof(v)); fin[nf++] = v;
        for (int w = 0; w < W; w++) covF[w] |= ballB[v][w];
        for (int w = 0; w < HW; w++) hitF[w] |= S[v][w];
    }
    for (int w = 0; w < W; w++) if (~covF[w]) { stat_fail[1]++; return 0; }
    for (int w = 0; w < HW; w++) if ((hitF[w] & hm[w]) != hm[w]) { stat_fail[1]++; return 0; }
    if (!selfok(fin, 16)) { stat_fail[2]++; return 0; }
    memcpy(outN, fin, sizeof(int) * 16); *outSz = 16;
    (void)cur;
    return 1;
}

