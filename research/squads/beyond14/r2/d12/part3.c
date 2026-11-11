static el relnz(void) { el x; do { x.a = rnd() % M; x.j = rnd() % K_; } while (x.a == 0); return x; }
static void setpair(int i, el x) { S[i] = x; S[i + 1] = bof(x); }
static int readsol2(const char *fn) {   /* orbit-form solution: e, x1, b(x1), x2, b(x2) (readsol order) */
    if (!readsol(fn)) return 0;
    for (int q = 0; q < 2; q++) { el y = bof(S[1 + 2 * q]); if (S[2 + 2 * q].a != y.a || S[2 + 2 * q].j != y.j) return 0; }
    return S[0].a == 0 && S[0].j == 0;
}
int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: hmetab d D seconds seed K outfile m k r\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (u64)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int Kc = atoi(argv[5]); const char *out = argv[6]; M = atoll(argv[7]); K_ = atoll(argv[8]); R_ = atoll(argv[9]);
    if (d != 5) { fprintf(stderr, "this variant is for d = 5 (e + two orbit pairs)\n"); return 2; }
    if (M % 2 == 0 || mpow(R_, K_, M) != 1 % M) { fprintf(stderr, "need m odd and r^k = 1 mod m\n"); return 2; }
    N = M * K_; RP = malloc(sizeof(i64) * K_); for (i64 j = 0; j < K_; j++) RP[j] = mpow(R_, j, M);
    W = (M + 63) / 64; W2 = (2 * M + 63) / 64 + 2; lastmask = (M % 64) ? ((1ULL << (M % 64)) - 1) : ~0ULL;
    HA = malloc(K_ * W * 8); HB = malloc(K_ * W * 8);
    SA = aligned_alloc(64, ((K_ * W * 8 + 63) / 64) * 64); SB = aligned_alloc(64, ((K_ * W * 8 + 63) / 64) * 64);
    DBL = aligned_alloc(64, ((K_ * W2 * 8 + 63) / 64) * 64);
    if (!SA || !SB || !DBL) { fprintf(stderr, "out of memory\n"); return 2; }
    int th = getenv("THREADS") ? atoi(getenv("THREADS")) : 1; omp_set_num_threads(th);
    double T0 = getenv("T0") ? atof(getenv("T0")) : 8.0, T1 = getenv("T1") ? atof(getenv("T1")) : 1.0;
    int reheat = getenv("REHEAT") ? atoi(getenv("REHEAT")) : 400;
    int targp = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
    S[0].a = 0; S[0].j = 0;
    if (getenv("EVAL")) { if (!readsol2(getenv("EVAL"))) { fprintf(stderr, "bad EVAL file (orbit form?)\n"); return 2; }
        double t = now(); i64 c = cost(); printf("EVAL cost=%lld (%.2fs) N=%lld\n", (long long)c, now() - t, (long long)N); return 0; }
    if (getenv("START")) { if (!readsol2(getenv("START"))) { fprintf(stderr, "bad START file (orbit form?)\n"); return 2; } }
    else for (int q = 0; q < 2; q++) { int i = 1 + 2 * q; do { setpair(i, relnz()); } while (!pairok(i)); }
    double t0 = now(); i64 cur = cost(), best = cur; el BS[64]; memcpy(BS, S, sizeof S);
    fprintf(stderr, "hmetab d=%d D=%d meta %lld %lld %lld N=%lld: start cost=%lld (%.2fs per eval)\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)cur, now() - t0);
    long evals = 1, moves = 0, since = 0; char bf[600]; snprintf(bf, sizeof bf, "%s.best", out);
    while (best > 0 && now() - t0 < secs) {
        double fr = (now() - t0) / secs; double T = T0 * pow(T1 / T0, fr);
        int q = rnd() % 2, i = 1 + 2 * q; el oldx = S[i];
        int ntarg = 0; el U[64]; int US[64];
        if (targp > 0 && cur > 0) { cost(); evals++;
            for (int c = 0; c < Kc; c++) { int side = (D % 2 == 0 || (lastA > 0 && (lastB == 0 || rnd() % (lastA + lastB) < (u64)lastA))) ? 0 : 1;
                if ((int)(rnd() % 100) < targp && hole(side, &U[ntarg])) US[ntarg++] = side; } }
        i64 bcost = -1; el bc = oldx;
        for (int c = 0; c < Kc; c++) {
            el x; int ok = 0;
            for (int tries = 0; tries < 50 && !ok; tries++) {
                if (c < ntarg && tries == 0) x = target2(i, US[c], U[c]); else x = relnz();
                if (x.a == 0) continue;
                setpair(i, x); if (pairok(i)) ok = 1;
            }
            if (!ok) continue;
            i64 v = cost(); evals++;
            if (bcost < 0 || v < bcost) { bcost = v; bc = x; }
        }
        moves++; since++;
        if (bcost < 0) { setpair(i, oldx); continue; }
        if (bcost <= cur || exp(-(double)(bcost - cur) / (T * (1 + 0.02 * cur))) > (rnd() % 1000000) / 1e6) { setpair(i, bc); cur = bcost; }
        else setpair(i, oldx);
        if (cur < best) { best = cur; memcpy(BS, S, sizeof S); since = 0; writesol(bf);
            fprintf(stderr, "t=%.0f moves=%ld evals=%ld best=%lld T=%.2f\n", now() - t0, moves, evals, (long long)best, T); }
        if (since > reheat) { memcpy(S, BS, sizeof S); cur = best; since = 0; }
    }
    memcpy(S, BS, sizeof S);
    if (best == 0) { i64 c = cost(); if (c != 0) { fprintf(stderr, "re-evaluation failed (%lld)\n", (long long)c); return 1; } writesol(out); }
    printf("RESULT d=%d D=%d group=meta %lld %lld %lld N=%lld vertices=%lld best=%lld evals=%ld time=%.1f orbit=2,2,1\n", d, D, (long long)M, (long long)K_, (long long)R_, (long long)N, (long long)(2 * N), (long long)best, evals, now() - t0);
    return 0;
}
