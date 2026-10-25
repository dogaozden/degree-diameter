/* ---- LNS (card c5): destroy a region of sigma, repair it by a short restricted anneal, accept by the rule ---- */
static double envd(const char *k, double d) { return getenv(k) ? atof(getenv(k)) : d; }
static int *RP, nRP, *RL, nRL, *Qb, *seenV, *seenL, *bL, *bP, *bS, *bI, *oL, *oP, *oS, *oI;
static uint8_t *inP;
static void snapTo(int *dl, int *dp, int *ds, int *di) { memcpy(dl, ln, 4L * n * dg); memcpy(dp, pt, 4L * n * dg); memcpy(ds, sig, 4L * n); memcpy(di, sinv, 4L * n); }
static void snapFrom(const int *sl, const int *sp, const int *ss, const int *si) { memcpy(ln, sl, 4L * n * dg); memcpy(pt, sp, 4L * n * dg); memcpy(sig, ss, 4L * n); memcpy(sinv, si, 4L * n); }
static long evalc(void) {
    for (int i = 0; i < nhot; i++) ishot[hot[i]] = 0; nhot = 0;
    for (int i = 0; i < nhv; i++) ishv[hv[i]] = 0; nhv = 0;
    collect = 1; long c = total(); collect = 0; return c;
}
static void addP(int p, int K) { if (nRP < K && !inP[p]) { inP[p] = 1; RP[nRP++] = p; } }
/* ball in the incidence graph around vertex c0 (v < n point, v >= n line); region = points of the visited vertices (a line
   contributes its sigma-preimage) */
static void regVertexBFS(int c0, int K) {
    int qh = 0, qt = 0; memset(seenV, 0, 4L * V);
    Qb[qt++] = c0; seenV[c0] = 1;
    while (qh < qt && nRP < K) {
        int x = Qb[qh++];
        addP(x < n ? x : sinv[x - n], K);
        int off = x < n ? n : 0; const int *nb = x < n ? pt + x * dg : ln + (x - n) * dg;
        int j0= rnd() % dg;
        for (int j = 0; j < dg; j++) { int y = nb[(j + j0) % dg] + off; if (!seenV[y]) { seenV[y] = 1; Qb[qt++] = y; } }
    }
}
/* ball in the line graph (lines sharing a point) around line l0; region = sigma-preimages of the lines */
static void regLineBFS(int l0, int K) {
    int qh = 0, qt = 0; memset(seenL, 0, 4L * n);
    Qb[qt++] = l0; seenL[l0] = 1;
    while (qh < qt && nRP < K) {
        int l = Qb[qh++];
        addP(sinv[l], K);
        int j0 = rnd() % dg;
        for (int j = 0; j < dg; j++) {
            int p = ln[l * dg + (j + j0) % dg]; int k0 = rnd() % dg;
            for (int k = 0; k < dg; k++) { int l2 = pt[p * dg + (k + k0) % dg]; if (!seenL[l2]) { seenL[l2] = 1; Qb[qt++] = l2; } }
        }
    }
}
static int hotVertex(void) { return nhv ? hv[rnd() % nhv] : (int)(rnd() % V); }
static int hotLine(void) { int v = hotVertex(); return v >= n ? v - n : sig[v]; }
static void buildRegion(int type, int K) {
    nRP = 0;
    if (type == 0) regVertexBFS(hotVertex(), K);                       /* ball around a hot vertex */
    else if (type == 1) regLineBFS(hotLine(), K);                      /* sigma-preimage of lines near a hot line */
    else if (type == 2) regVertexBFS((int)(rnd() % n), K);             /* ball around a random point */
    else if (type == 3) { while (nRP < K) addP((int)(rnd() % n), K); } /* random points */
    else { regVertexBFS(hotVertex(), K / 2); regLineBFS(hotLine(), K); } /* mixed */
    nRL = nRP; for (int i = 0; i < nRP; i++) RL[i] = sig[RP[i]];
}
static void clearRegion(void) { for (int i = 0; i < nRP; i++) inP[RP[i]] = 0; }
/* a degree-preserving flag swap with both lines in the region lines RL */
static int tryFlag(int *f) {
    for (int tr = 0; tr < 60; tr++) {
        int l1 = RL[rnd() % nRL], l2 = RL[rnd() % nRL]; if (l1 == l2) continue;
        int p1 = ln[l1 * dg + rnd() % dg], p2 = ln[l2 * dg + rnd() % dg];
        if (p1 == p2 || has(ln + l2 * dg, p1) || has(ln + l1 * dg, p2)) continue;
        f[0] = l1; f[1] = p1; f[2] = l2; f[3] = p2; return 1;
    }
    return 0;
}
static void applyFlag(const int *f) { int l1 = f[0], p1 = f[1], l2 = f[2], p2 = f[3];
    repl(ln + l1 * dg, p1, p2); repl(ln + l2 * dg, p2, p1); repl(pt + p1 * dg, l1, l2); repl(pt + p2 * dg, l2, l1); }
static void undoFlag(const int *f) { int l1 = f[0], p1 = f[1], l2 = f[2], p2 = f[3];
    repl(ln + l1 * dg, p2, p1); repl(ln + l2 * dg, p1, p2); repl(pt + p1 * dg, l2, l1); repl(pt + p2 * dg, l1, l2); }
/* DESTROY: random permutation of sigma among the region points (their image set RL is kept), optional flag shuffles */
static int DMODE = 0, SMAX = 3;   /* DMODE 0: full random permutation of sigma on RP; 1: SMAX..1 random swaps inside RP */
static void destroy(double pflip, int nflip) {
    if (DMODE == 1) { int s = 1 + (int)(rnd() % SMAX);
        for (int t = 0; t < s; t++) { int a = RP[rnd() % nRP], b = RP[rnd() % nRP]; if (a == b) continue;
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b; } }
    else {
    for (int i = nRP - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = RL[i]; RL[i] = RL[j]; RL[j] = t; }
    for (int i = 0; i < nRP; i++) { int p = RP[i], l = RL[i]; sig[p] = l; sinv[l] = p; } }
    if (urand() < pflip) { int f[4]; for (int t = 0; t < nflip; t++) if (tryFlag(f)) applyFlag(f); }
}
/* REPAIR: low-temperature anneal restricted to the region (sigma swaps inside RP, flag swaps on RL lines).
   Returns the lowest exact cost seen (the state is left at the last state achieving it). */
static long repair(int NREP, double Tr0, double Tr1, double PFR) {
    long cur = evalc(), bestc = cur;
    snapTo(bL, bP, bS, bI);
    int f[4];
    for (int it = 0; it < NREP && bestc > 0; it++) {
        double T = Tr0 * pow(Tr1 / Tr0, (double)it / NREP);
        if (urand() >= PFR) {
            int a = RP[rnd() % nRP], b = RP[rnd() % nRP]; if (a == b) continue;
            int la = sig[a], lb = sig[b]; sig[a] = lb; sig[b] = la; sinv[lb] = a; sinv[la] = b;
            long c2 = evalc();
            if (c2 <= cur || urand() < exp((cur - c2) / T)) cur = c2;
            else { sig[a] = la; sig[b] = lb; sinv[la] = a; sinv[lb] = b; }
        } else {
            if (!tryFlag(f)) continue;
            applyFlag(f);
            long c2 = evalc();
            if (c2 <= cur || urand() < exp((cur - c2) / T)) cur = c2;
            else undoFlag(f);
        }
        if (cur <= bestc) { bestc = cur; snapTo(bL, bP, bS, bI); }
    }
    snapFrom(bL, bP, bS, bI);
    return bestc;
}


/* REP=1 mode: exhaustive re-optimisation of sigma on the region (all m! permutations of RL over RP, Heap's algorithm).
   Leaves the state at the best permutation; ties are broken uniformly (reservoir). Returns the best cost. */
static void applyPerm(const int *A) { for (int j = 0; j < nRP; j++) { sig[RP[j]] = A[j]; sinv[A[j]] = RP[j]; } }
static long enumRegion(long curc) {
    int m = nRP; int A[64], cc[64], B[64];
    for (int i = 0; i < m; i++) { A[i] = RL[i]; B[i] = RL[i]; cc[i] = 0; }
    long bestc = curc; int ties = 1;
    int i = 1;
    while (i < m && bestc > 0) {
        if (cc[i] < i) {
            if (i % 2 == 0) { int t = A[0]; A[0] = A[i]; A[i] = t; } else { int t = A[cc[i]]; A[cc[i]] = A[i]; A[i] = t; }
            applyPerm(A); long c2 = evalc();
            if (c2 < bestc) { bestc = c2; ties = 1; memcpy(B, A, 4L * m); }
            else if (c2 == bestc) { ties++; if (rnd() % ties == 0) memcpy(B, A, 4L * m); }
            cc[i]++; i = 1;
        } else { cc[i] = 0; i++; }
    }
    applyPerm(B);
    return bestc;
}

int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d", &n, &dg) != 2) return 1; V = 2 * n;
    ln = malloc(4L * n * dg); for (int i = 0; i < n * dg; i++) if (fscanf(f, "%d", &ln[i]) != 1) return 1;
    sig = malloc(4L * n); sinv = malloc(4L * n); for (int i = 0; i < n; i++) if (fscanf(f, "%d", &sig[i]) != 1) return 1; fclose(f);
    for (int i = 0; i < n; i++) sinv[sig[i]] = i;
    pt = malloc(4L * n * dg); int *fill = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int k = 0; k < dg; k++) { int p = ln[l * dg + k]; pt[p * dg + fill[p]++] = l; }
    for (int p = 0; p < n; p++) if (fill[p] != dg) { fprintf(stderr, "point %d degree %d\n", p, fill[p]); return 1; }
    R0 = malloc(24L * V); F0 = malloc(24L * V); N0 = malloc(24L * V); for (int d = 0; d < 6; d++) { C1[d] = malloc(8L * V); C2[d] = malloc(8L * V); }
    MU = 0;
    hot = malloc(4L * n); ishot = calloc(n, 1); nhot = 0; hv = malloc(8L * n); ishv = calloc(2 * n, 1); nhv = 0;
    RP = malloc(4L * n); RL = malloc(4L * n); Qb = malloc(4L * V); seenV = malloc(4L * V); seenL = malloc(4L * n); inP = calloc(n, 1);
    bL = malloc(4L * n * dg); bP = malloc(4L * n * dg); bS = malloc(4L * n); bI = malloc(4L * n);
    oL = malloc(4L * n * dg); oP = malloc(4L * n * dg); oS = malloc(4L * n); oI = malloc(4L * n);
    long c = evalc(); long best = c;
    printf("n=%d dg=%d start cost=%ld\n", n, dg, c); fflush(stdout);
    if (c == 0) { if (getenv("OUT0")) save(getenv("OUT0"), ln, sig); printf("FAIL0 at start\n"); return 0; }
    double secs = envd("SECS", 600), TR0 = envd("TR0", 1.0), TR1 = envd("TR1", 0.15), PFR = envd("PFR", 0.3), PFD = envd("PFD", 0.5);
    double TACC = envd("TACC", 0.7); int NREP = (int)envd("NREP", 150), NFLIP = (int)envd("NFLIP", 3);
    int KMIN = (int)envd("KMIN", 20), KMAX = (int)envd("KMAX", 80);
    DMODE = (int)envd("DMODE", 0); SMAX = (int)envd("SMAX", 3);
    int REP = (int)envd("REP", 0);
    const char *TYPES = getenv("TYPES") ? getenv("TYPES") : "01234"; int nty = strlen(TYPES);
    if (getenv("OUT")) save(getenv("OUT"), ln, sig);
    long tryc[5] = {0}, accc[5] = {0}, imp[5] = {0}, minc[5]; for (int i = 0; i < 5; i++) minc[i] = 1L << 40;
    long it = 0, nacc = 0, nworse = 0; clock_t t0 = clock();
    while (best > 0) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
        it++;
        long cOld = c;
        snapTo(oL, oP, oS, oI);
        int type = TYPES[rnd() % nty] - '0';
        int K = KMIN + (int)(rnd() % (unsigned)(KMAX - KMIN + 1)); if (K > n) K = n;
        buildRegion(type, K);
        long cDes, cRep;
        if (REP == 1) { cDes = c; cRep = enumRegion(c); }
        else { destroy(PFD, NFLIP);
        cDes = evalc();
        cRep = repair(NREP, TR0, TR1, PFR); }
        if (getenv("DBG")) printf("DBG type=%d K=%d nRP=%d cOld=%ld cDes=%ld cRep=%ld\n", type, K, nRP, cOld, cDes, cRep);
        int acc = cRep <= cOld ? 1 : (urand() < exp(-(double)(cRep - cOld) / TACC));
        if (!acc) snapFrom(oL, oP, oS, oI);
        else { nacc++; if (cRep > cOld) nworse++; }
        c = evalc();   /* refresh hot lists; c equals cRep (accepted) or cOld (rejected) */
        clearRegion();
        tryc[type]++; if (acc) accc[type]++; if (c < minc[type]) minc[type] = c;
        if (c < best) {
            best = c; imp[type]++;
            if (getenv("OUT")) save(getenv("OUT"), ln, sig);
            printf("t=%.0f it=%ld cost=%ld type=%d K=%d\n", el, it, c, type, K); fflush(stdout);
        }
        if (best == 0) { if (getenv("OUT0")) save(getenv("OUT0"), ln, sig); printf("FAIL0 reached at it=%ld\n", it); break; }
        if (it % 50 == 0) {
            printf("it=%ld t=%.0f cur=%ld best=%ld acc=%ld worse=%ld |", it, el, c, best, nacc, nworse);
            for (int ty = 0; ty < 5; ty++) if (tryc[ty]) printf(" T%d %ld/%ld min%ld", ty, accc[ty], tryc[ty], minc[ty]);
            printf("\n"); fflush(stdout);
        }
    }
    printf("RESULT best=%ld iters=%ld accepted=%ld worse_accepted=%ld\n", best, it, nacc, nworse);
    return 0;
}
