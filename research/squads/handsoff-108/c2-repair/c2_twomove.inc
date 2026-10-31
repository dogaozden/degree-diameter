/* c2-repair (handsoff-108): exact two-move neighbourhood of a given state.  Included into haar_c2.c before orbit_main.
 * Usage: ORBIT="3 3 1" ORBW=3 TWOMOVE=1 TWOSTATE="s0 ... s9" [C2K=100] [C2M=2] [C2SECS=3000] ./haar_c2 10 8 1 1 8 out.txt psl 23 97
 * Energy = raw uncovered + (ORBW-1) * uncovered alpha-fixed elements (same as the annealer).
 * Moves, all evaluated exactly (no sampling):
 *   (1) single orbit replacement, all alpha-orbits of every slot, top C2K per slot kept;
 *   (2) pair of orbit replacements (slots a < b): all C2K x C2K pairs of the top lists (distinctness checked);
 *   (3) right multiplication of two orbits by the same alpha-fixed element c (alpha(x c) = alpha(x) c);
 *   (4) replace the fixed letter e by an alpha-fixed element c; the C2M best c get the full (1)+(2) neighbourhood.
 * The loop accepts the best strictly improving move and restarts; it stops when no move improves.
 */
typedef struct { long long e; int o[3]; } c2cand;
static uint64_t *c2sv[2];
static uint32_t *c2XF[3], *c2XI[3];

static long long c2_eval(ctx *c, uint32_t **tf, uint32_t **ti, long long bnd) {
    double sc; long long r = cost_any(c, tf, ti, &sc, c2sv, &bnd, 0);
    if (r < 0) return -1;                     /* abandoned: raw >= bnd */
    return ORBW > 1 ? r + (ORBW - 1) * fixmiss(c2sv) : r;
}
static void c2_sync(void) { for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); mktab(S[i], TF[i], TI[i]); } }
static int c2_distinct(const int *s) { for (int i = 0; i < d; i++) for (int u = 0; u < i; u++) if (s[u] == s[i]) return 0; return 1; }
static int c2_orbit_ok(const int *o) { for (int r = 0; r < OK_; r++) if (alpha(o[r]) != o[(r + 1) % OK_]) return 0; return 1; }

/* the K best single-orbit replacements of slot j of the current S (ascending energy); returns how many */
static int c2_scan(ctx *c, int j, int K, c2cand *top, long long *nev) {
    uint32_t *tf[MAXD], *ti[MAXD];
    memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
    int cnt = 0;
    for (long long x = 0; x < N; x++) {
        int o[MAXD];
        if (!orbit_of((int)x, o)) continue;
        if (o[1] < x || o[2] < x) continue;          /* one representative per orbit (k = 3) */
        if (!orbit_free(o, j)) continue;
        for (int r = 0; r < OK_; r++) { mktab(o[r], c2XF[r], c2XI[r]); tf[ostart(j) + r] = c2XF[r]; ti[ostart(j) + r] = c2XI[r]; }
        long long bnd = cnt < K ? NOBOUND : top[K - 1].e;
        long long e = c2_eval(c, tf, ti, bnd); (*nev)++;
        if (e < 0) continue;
        if (cnt == K && e >= top[K - 1].e) continue;
        if (cnt < K) cnt++;
        int p = cnt - 1;
        while (p > 0 && top[p - 1].e > e) { top[p] = top[p - 1]; p--; }
        top[p].e = e; memcpy(top[p].o, o, sizeof(int) * OK_);
    }
    return cnt;
}
typedef struct { uint32_t *f[3], *i[3]; } c2tab;
static c2tab c2_build(const int *o) { c2tab t; for (int r = 0; r < OK_; r++) { t.f[r] = malloc(4 * NROWS); t.i[r] = malloc(4 * NROWS); mktab(o[r], t.f[r], t.i[r]); } return t; }
static void c2_free(c2tab *t) { for (int r = 0; r < OK_; r++) { free(t->f[r]); free(t->i[r]); } }

/* best pair of replacements (slots a < b) from the top lists; counts pairs with energy < E0 and = E0 */
static long long c2_pairs(ctx *c, int a, int b, int nA, const c2cand *tA, int nB, const c2cand *tB, long long E0,
                          long long *nless, long long *neq, long long *nev, int *bestS) {
    c2tab *TA = malloc(sizeof(c2tab) * (nA ? nA : 1)), *TB = malloc(sizeof(c2tab) * (nB ? nB : 1));
    for (int i = 0; i < nA; i++) TA[i] = c2_build(tA[i].o);
    for (int i = 0; i < nB; i++) TB[i] = c2_build(tB[i].o);
    uint32_t *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
    long long best = E0 + 1; *nless = *neq = 0;
    for (int ia = 0; ia < nA; ia++) for (int ib = 0; ib < nB; ib++) {
        int s2[MAXD]; memcpy(s2, S, sizeof(int) * d);
        for (int r = 0; r < OK_; r++) { s2[ostart(a) + r] = tA[ia].o[r]; s2[ostart(b) + r] = tB[ib].o[r]; }
        if (!c2_distinct(s2)) continue;
        for (int r = 0; r < OK_; r++) { tf[ostart(a) + r] = TA[ia].f[r]; ti[ostart(a) + r] = TA[ia].i[r];
                                        tf[ostart(b) + r] = TB[ib].f[r]; ti[ostart(b) + r] = TB[ib].i[r]; }
        long long e = c2_eval(c, tf, ti, E0 + 1); (*nev)++;
        if (e < 0) continue;
        if (e < E0) (*nless)++; else if (e == E0) (*neq)++;
        if (e < best) { best = e; if (bestS) memcpy(bestS, s2, sizeof(int) * d); }
    }
    for (int i = 0; i < nA; i++) c2_free(&TA[i]);
    for (int i = 0; i < nB; i++) c2_free(&TB[i]);
    free(TA); free(TB);
    return best;
}

/* evaluate one explicit set (generic tables) */
static long long c2_eval_set(ctx *c, const int *s, long long bnd) {
    uint32_t *tf[MAXD], *ti[MAXD]; uint32_t *bf[MAXD], *bi[MAXD];
    for (int i = 0; i < d; i++) { bf[i] = malloc(4 * NROWS); bi[i] = malloc(4 * NROWS); mktab(s[i], bf[i], bi[i]); tf[i] = bf[i]; ti[i] = bi[i]; }
    long long e = c2_eval(c, tf, ti, bnd);
    for (int i = 0; i < d; i++) { free(bf[i]); free(bi[i]); }
    return e;
}

/* full neighbourhood of the current S (moves 1-3). Returns the best energy found (may be >= E0); bestS gets its set. */
static long long c2_neigh(ctx *c, int K, long long E0, int *bestS, long long *nev, const char *tag) {
    c2cand *top[MAXD]; int cnt[MAXD];
    long long best = 1LL << 60; int bS[MAXD]; memcpy(bS, S, sizeof(int) * d);
    for (int j = 0; j < OM; j++) {
        top[j] = malloc(sizeof(c2cand) * K);
        cnt[j] = c2_scan(c, j, K, top[j], nev);
        long long bj = cnt[j] ? top[j][0].e : (1LL << 60);
        printf("C2 %s single slot %d: best energy %lld (top %d kept, worst kept %lld)\n", tag, j, bj, cnt[j],
               cnt[j] ? top[j][cnt[j] - 1].e : -1LL);
        fflush(stdout);
        if (bj < best) { best = bj; memcpy(bS, S, sizeof(int) * d);
            for (int r = 0; r < OK_; r++) bS[ostart(j) + r] = top[j][0].o[r]; }
    }
    for (int a = 0; a < OM; a++) for (int b = a + 1; b < OM; b++) {
        long long nl = 0, ne = 0; int pS[MAXD];
        long long pb = c2_pairs(c, a, b, cnt[a], top[a], cnt[b], top[b], E0, &nl, &ne, nev, pS);
        printf("C2 %s pair slots %d,%d: best energy %lld, pairs below E0 %lld, equal to E0 %lld (of %d x %d)\n",
               tag, a, b, pb, nl, ne, cnt[a], cnt[b]);
        fflush(stdout);
        if (pb < best) { best = pb; memcpy(bS, pS, sizeof(int) * d); }
    }
    /* (3) right multiplication of two orbits by one alpha-fixed element */
    long long nr = 0, nrb = 0; long long rbest = 1LL << 60; int rS[MAXD];
    for (long long ci = 0; ci < NFIX; ci++) {
        int cc = FIXL[ci];
        for (int a = 0; a < OM; a++) for (int b = a + 1; b < OM; b++) {
            int s2[MAXD]; memcpy(s2, S, sizeof(int) * d);
            for (int r = 0; r < OK_; r++) { s2[ostart(a) + r] = gmul(S[ostart(a) + r], cc); s2[ostart(b) + r] = gmul(S[ostart(b) + r], cc); }
            if (!c2_orbit_ok(&s2[ostart(a)]) || !c2_orbit_ok(&s2[ostart(b)]) || !c2_distinct(s2)) continue;
            long long e = c2_eval_set(c, s2, E0 + 1); (*nev)++; nr++;
            if (e < 0) continue;
            if (e < E0) nrb++;
            if (e < rbest) { rbest = e; memcpy(rS, s2, sizeof(int) * d); }
        }
    }
    printf("C2 %s right-mult pairs: %lld tried, best energy %lld, below E0 %lld\n", tag, nr, rbest, nrb);
    fflush(stdout);
    if (rbest < best) { best = rbest; memcpy(bS, rS, sizeof(int) * d); }
    for (int j = 0; j < OM; j++) free(top[j]);
    memcpy(bestS, bS, sizeof(int) * d);
    return best;
}

static int c2_main(ctx *c0, const char *out) {
    (void)out;
    const char *st = getenv("TWOSTATE");
    if (!st) { fprintf(stderr, "TWOMOVE needs TWOSTATE=\"10 element indices\"\n"); return 2; }
    { char buf[512]; strncpy(buf, st, sizeof buf - 1); buf[sizeof buf - 1] = 0; char *p = buf; int n = 0;
      for (char *tok = strtok(p, " \t,"); tok && n < d; tok = strtok(NULL, " \t,")) S[n++] = atoi(tok);
      if (n != d) { fprintf(stderr, "TWOSTATE needs %d indices\n", d); return 2; } }
    for (int i = 0; i < d; i++) if (S[i] < 0 || S[i] >= N) { fprintf(stderr, "index out of range\n"); return 2; }
    if (!c2_distinct(S)) { fprintf(stderr, "TWOSTATE not a set\n"); return 2; }
    for (int j = 0; j < OM; j++) if (!c2_orbit_ok(&S[ostart(j)])) { fprintf(stderr, "slot %d is not an alpha-chain\n", j); return 2; }
    int K = getenv("C2K") ? atoi(getenv("C2K")) : 100, M = getenv("C2M") ? atoi(getenv("C2M")) : 2;
    double SECS = getenv("C2SECS") ? atof(getenv("C2SECS")) : 3000;
    for (int r = 0; r < OK_; r++) { c2XF[r] = malloc(4 * NROWS); c2XI[r] = malloc(4 * NROWS); }
    c2sv[0] = zalloc64(BITBYTES); c2sv[1] = zalloc64(BITBYTES);
    c2_sync();
    long long nev = 0; double t0 = now();
    long long E0 = c2_eval(c0, TF, TI, NOBOUND);     /* energy (includes the fixed-element term when ORBW > 1) */
    printf("C2 start energy %lld (ORBW=%d, K=%d, M=%d)\n", E0, ORBW, K, M); fflush(stdout);
    long long startE = E0;
    int round = 0;
    while (E0 > 0 && now() - t0 < SECS) {
        round++;
        int bS[MAXD];
        long long b = c2_neigh(c0, K, E0, bS, &nev, "base");
        if (b < E0) {
            memcpy(S, bS, sizeof(int) * d); c2_sync(); E0 = b;
            printf("C2 round %d IMPROVED to energy %lld (%.0f s, %lld evals)\n", round, E0, now() - t0, nev); fflush(stdout);
            continue;
        }
        /* (4) fixed letter: rank every alpha-fixed c replacing e by energy, then give the best M the full neighbourhood */
        int okS[MAXD]; memcpy(okS, S, sizeof(int) * d);
        long long *ce = malloc(sizeof(long long) * (NFIX + 1)); long long nlo = 0, cbest = 1LL << 60; long long nbelow = 0;
        for (long long ci = 0; ci < NFIX; ci++) {
            int s2[MAXD]; memcpy(s2, S, sizeof(int) * d); s2[0] = FIXL[ci];
            if (!c2_distinct(s2)) { ce[ci] = -1; continue; }
            ce[ci] = c2_eval_set(c0, s2, NOBOUND); nev++; nlo++;
            if (ce[ci] >= 0 && ce[ci] < cbest) cbest = ce[ci];
            if (ce[ci] >= 0 && ce[ci] < E0) nbelow++;
        }
        printf("C2 round %d fixed-letter: %lld alpha-fixed letters tried (E0+1 bound), best %lld, below E0 %lld\n",
               round, nlo, cbest, nbelow); fflush(stdout);
        /* pick the M smallest */
        int used_m = 0;
        for (int m = 0; m < M; m++) {
            long long bv = 1LL << 60; long long bi = -1;
            for (long long ci = 0; ci < NFIX; ci++) if (ce[ci] >= 0 && ce[ci] < bv) { bv = ce[ci]; bi = ci; }
            if (bi < 0) break;
            ce[bi] = -1;
            int s2[MAXD]; memcpy(s2, okS, sizeof(int) * d); s2[0] = FIXL[bi];
            memcpy(S, s2, sizeof(int) * d); c2_sync();
            int bS2[MAXD];
            char tag[64]; snprintf(tag, sizeof tag, "fixed-letter %d (c=%d, E=%lld)", m, FIXL[bi], bv);
            long long b2 = c2_neigh(c0, K, E0, bS2, &nev, tag);
            used_m++;
            if (b2 < E0) { memcpy(S, bS2, sizeof(int) * d); c2_sync(); E0 = b2; printf("C2 IMPROVED via fixed letter to %lld\n", E0); fflush(stdout); goto next_round; }
            memcpy(S, okS, sizeof(int) * d); c2_sync();
        }
        (void)used_m;
        free(ce);
        printf("C2 round %d: no move improves energy %lld (%.0f s, %lld evals)\n", round, E0, now() - t0, nev); fflush(stdout);
        break;
    next_round:
        free(ce);
    }
    printf("C2 RESULT start %lld final %lld rounds %d evals %lld time %.0f\n", startE, E0, round, nev, now() - t0);
    fflush(stdout);
    if (E0 == 0) {   /* a cost-0 state is written by the normal path */
        c2_sync();
        if (!check_and_write(c0, out)) return 1;
    }
    return E0 == 0 ? 0 : 1;
}
