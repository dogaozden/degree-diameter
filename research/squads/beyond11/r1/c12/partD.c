int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: haar_sd d D seconds seed K outfile sl|psl p n   (env SD=1 SDSIZES=\"6 6\")\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]); u64 seed = strtoull(argv[4], 0, 10);
    int K = atoi(argv[5]); const char *out = argv[6];
    PSL = !strcmp(argv[7], "psl"); if (!PSL && strcmp(argv[7], "sl")) { fprintf(stderr, "family sl or psl\n"); return 2; }
    P = atoi(argv[8]); NC = atoll(argv[9]);
    if (D < 3 || d < 2 || d > MAXD || K < 1 || K > 64) { fprintf(stderr, "need D >= 3, 2 <= d <= %d, 1 <= K <= 64\n", MAXD); return 2; }
    if (D % 2 == 0) { fprintf(stderr, "SD mode is for odd D\n"); return 2; }
    for (int t = 2; t * t <= P; t++) if (P % t == 0) { fprintf(stderr, "p must be prime\n"); return 2; }
    if (P < 5) { fprintf(stderr, "p >= 5\n"); return 2; }
    if (gcdl(P, NC) != 1) { fprintf(stderr, "gcd(p, n) must be 1\n"); return 2; }
    HALF = (P - 1) / 2;
    sprintf(SPEC, "%s %d", PSL ? "psl" : "sl", P);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    INV = malloc(sizeof(int) * P); INV[0] = 0;
    for (int x = 1; x < P; x++) INV[x] = (int)ipow_mod(x, P - 2, P);
    L = (i64)P * NC; R = PSL ? ((i64)P * P - 1) / 2 : (i64)P * P - 1; NG = R * L;
    LW = (L + 63) / 64; LW8 = (LW + 7) / 8 * 8; RW = (2 * LW + 17 + 7) / 8 * 8;
    LASTMASK = (L & 63) ? (1ULL << (L & 63)) - 1 : ~0ULL;
    CP = (i64)((__int128)NC * ipow_mod(NC % P, P - 2, P) % L);
    CN = 0;
    if (NC > 1) {
        i64 t = 0, nt = 1, r = NC, nr = P % NC;
        while (nr) { i64 qq = r / nr, x = t - qq * nt; t = nt; nt = x; x = r - qq * nr; r = nr; nr = x; }
        if (t < 0) t += NC; CN = (i64)((__int128)P * t % L);
    }
    if (crt(1, 0) % P != 1 || (NC > 1 && crt(1, 0) % NC != 0) || crt(0, 1) % P != 0 || (NC > 1 && crt(0, 1) % NC != 1)) { fprintf(stderr, "CRT setup failed\n"); return 2; }
    E_ID = (el){1, 0, 0, 1, 0};
    for (int t = 0; t < 200000; t++) { i64 g = (i64)(rnd() % (u64)NG); el x = eofidx(g);
        if (md((i64)x.a * x.d - (i64)x.b * x.c) != 1 || eidx(x) != g || !eeq(canon(x), x)) { fprintf(stderr, "index self-test failed at %lld\n", (long long)g); return 2; } }
    NTH = getenv("THREADS") ? atoi(getenv("THREADS")) : 1; if (NTH < 1) NTH = 1;
    PUSHMAX = (i64)1 << 24; if (NG * (i64)d / 512 < PUSHMAX) PUSHMAX = NG * (i64)d / 512;
    if (getenv("PUSHMAX")) PUSHMAX = atoll(getenv("PUSHMAX"));
    if (getenv("UCAP")) UCAP = atoi(getenv("UCAP"));
    BENCH = getenv("BENCH") ? atoi(getenv("BENCH")) : 0; LEVPOP = 0;
    for (int b = 0; b < 2; b++) { BUF[b] = aligned_alloc(64, (size_t)(R * RW * 8)); if (!BUF[b]) { fprintf(stderr, "out of memory\n"); return 2; } }
    LISTCAP = PUSHMAX + 64; LIST = malloc(sizeof(i64) * LISTCAP);
    ACC = malloc(sizeof(u64 *) * NTH); RB = malloc(sizeof(u64 *) * NTH);
    for (int t = 0; t < NTH; t++) { ACC[t] = aligned_alloc(64, 8 * (LW8 + 16)); RB[t] = aligned_alloc(64, 8 * (RW + 16)); }
    for (int j = 0; j < d; j++) { FR[j] = malloc(4 * R); FC[j] = malloc(4 * R); PS[j] = malloc(8 * R); PI[j] = malloc(8 * R); }
    fprintf(stderr, "group %s x Z_%lld, N=%lld (2N=%lld), memory %.2f GB\n", SPEC, (long long)NC, (long long)NG, (long long)(2 * NG),
            2.0 * R * RW * 8 / 1e9 + (double)LISTCAP * 8 / 1e9 + 24.0 * d * R / 1e9);
    signal(SIGTERM, on_term); signal(SIGINT, on_term);
    i64 *ULIST[64]; int UN[64];
    for (int t = 0; t < K; t++) ULIST[t] = malloc(sizeof(i64) * UCAP);
    UNC = malloc(sizeof(i64) * UCAP);
    double W = 1; for (int i = 1; i <= (D - 1) / 2; i++) W += d * pow(d - 1, 2 * i - 1);   /* even words <= D-1 */
    double mu = NG * exp(-W / NG);
    choose_alpha_sd();
    if (NC > 1) { i64 best = -1, bfix = (i64)1 << 60;
        for (i64 r = 2; r < NC; r++) { if (gcdl(r, NC) != 1 || ipow_mod(r, 3, NC) != 1) continue;
            i64 fx = gcdl(r - 1, NC); if (fx < bfix) { bfix = fx; best = r; } }
        AR = best < 0 ? 1 : best; }
    for (int t = 0; t < 1000; t++) { el x = randel(), y = randel();
        if (!eeq(tau(alpha(x)), alpha(tau(x))) || !eeq(alpha(alpha(alpha(x))), x) || !eeq(tau(tau(x)), x) || !eeq(alpha(emul(x, y)), emul(alpha(x), alpha(y)))) {
            fprintf(stderr, "alpha/tau self-test failed\n"); return 2; } }
    NSLOT = 1; SLOTPOS[0] = 0; SLOTSZ[0] = 1;
    if (getenv("SDSIZES")) { char buf[256]; snprintf(buf, sizeof buf, "%s", getenv("SDSIZES")); int pos = 1;
        for (char *tok = strtok(buf, " ,"); tok; tok = strtok(NULL, " ,")) { int s = atoi(tok);
            if (s != 1 && s != 2 && s != 3 && s != 6) { fprintf(stderr, "slot size must be 1,2,3 or 6\n"); return 2; }
            if (NSLOT >= MAXD) return 2; SLOTPOS[NSLOT] = pos; SLOTSZ[NSLOT] = s; pos += s; NSLOT++; }
        if (pos != d) { fprintf(stderr, "SDSIZES must sum to d-1 = %d\n", d - 1); return 2; } }
    else if (!getenv("EVAL")) { fprintf(stderr, "SDSIZES=\"s1 s2 ...\" needed (sizes 1,2,3,6 summing to d-1)\n"); return 2; }
    S[0] = E_ID;
    for (int u = 1; u < d; u++) S[u] = (el){0, 0, 0, 0, -1};
    { int need_lists = 0; for (int k = 1; k < NSLOT; k++) if (SLOTSZ[k] != 6) need_lists = 1;
      if (need_lists) { double tl = now(); build_lists(); fprintf(stderr, "lists: %lld/%lld/%lld elements with H-orbit size 1/2/3 (%.1fs)\n",
          (long long)NLIST[1], (long long)NLIST[2], (long long)NLIST[3], now() - tl); } }
    fprintf(stderr, "alpha: order 3, tau-commuting; z -> %lld z on Z_%lld; slots %d; W=%.6g mu=%.2f\n",
            (long long)AR, (long long)NC, NSLOT - 1, W, mu);
    if (getenv("EVAL")) {
        if (!read_sol(getenv("EVAL"), S)) { fprintf(stderr, "cannot read %s\n", getenv("EVAL")); return 2; }
        if (!eeq(S[0], E_ID)) { el a0 = einv(S[0]); for (int i = 0; i < d; i++) S[i] = emul(S[i], a0); }
        int selfdual = 1;
        for (int i = 0; i < d; i++) { el t = tau(S[i]); int f = 0; for (int u = 0; u < d; u++) f |= eeq(S[u], t); selfdual &= f; }
        for (int j = 0; j < d; j++) make_tables(j);
        int nu; double t0 = now(); i64 c1 = cost1(NOBOUND, ULIST[0], UCAP, &nu);
        printf("EVAL %s selfdual=%d onesided=%lld sd_cost=%lld time=%.3f mu=%.2f\n", getenv("EVAL"), selfdual, (long long)c1, (long long)(2 * c1), now() - t0, mu);
        return c1 == 0 ? 0 : 1;
    }
    if (getenv("START")) {
        if (!read_sol(getenv("START"), S)) { fprintf(stderr, "cannot read START\n"); return 2; }
        for (int k = 1; k < NSLOT; k++) { el o[8]; int n = horbit(S[SLOTPOS[k]], o);
            if (n != SLOTSZ[k]) { fprintf(stderr, "START: slot %d has H-orbit size %d, want %d\n", k, n, SLOTSZ[k]); return 2; }
            for (int i = 0; i < SLOTSZ[k]; i++) { int f = 0; for (int u = 0; u < n; u++) f |= eeq(o[u], S[SLOTPOS[k] + i]); if (!f) { fprintf(stderr, "START: slot %d not an H-orbit\n", k); return 2; } } }
    } else for (int k = 1; k < NSLOT; k++) { el o[8]; if (!random_hslot(k, o)) { fprintf(stderr, "no H-orbit for slot %d\n", k); return 2; }
        for (int i = 0; i < SLOTSZ[k]; i++) S[SLOTPOS[k] + i] = o[i]; }
    for (int j = 0; j < d; j++) make_tables(j);
    int TARGP = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 1.5, TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.15;
    double COOLSTEPS = getenv("COOLSTEPS") ? atof(getenv("COOLSTEPS")) : 4;
    i64 REHEATSTEPS = getenv("REHEATSTEPS") ? atoll(getenv("REHEATSTEPS")) : 60;
    double t0 = now();
    i64 c = cost_sd(NOBOUND, UNC, UCAP, &NUNC), best = c; el bestS[MAXD]; memcpy(bestS, S, sizeof(el) * d);
    i64 evals = 1, steps = 0, lastimp = 0, heat = 0;
    double T = TMAX, cE = (double)c / 2.0;
    fprintf(stderr, "start sd_cost=%lld (%.2fs)\n", (long long)c, now() - t0);
    char bestfile[1024]; snprintf(bestfile, sizeof bestfile, "%s.best", out);
    el cand[64][6];
    while (!stop_flag && now() - t0 < secs && best > 0) {
        int k = 1 + (int)(rnd() % (u64)(NSLOT - 1)); int sz = SLOTSZ[k], pos = SLOTPOS[k];
        AVOID = 0; for (int i = 0; i < sz; i++) AVOID |= 1ULL << (pos + i);
        int bad = 0;
        for (int t = 0; t < K; t++) {
            el x, o[8]; int ok = 0;
            if ((int)(rnd() % 100) < TARGP && targeted(&x)) ok = !eeq(x, E_ID) && horbit(x, o) == sz && hfree(o, sz, k);
            if (!ok) ok = random_hslot(k, o);
            if (!ok) { bad = 1; break; }
            memcpy(cand[t], o, sizeof(el) * sz);
        }
        AVOID = 0;
        if (bad) { steps++; continue; }
        el keep[6]; memcpy(keep, S + pos, sizeof(el) * sz);
        i64 bound = NOBOUND, cs[64]; int bt = -1;
        for (int t = 0; t < K && !stop_flag; t++) {
            for (int i = 0; i < sz; i++) S[pos + i] = cand[t][i];
            retab_slot(k);
            i64 r = cost_sd(bound, ULIST[t], UCAP, &UN[t]); evals++;
            cs[t] = r < 0 ? NOBOUND : r;
            if (r >= 0 && r < bound) { bound = r; bt = t; }
        }
        if (bt < 0) { for (int i = 0; i < sz; i++) S[pos + i] = keep[i]; retab_slot(k); steps++; continue; }
        double bE = (double)cs[bt] / 2.0;
        int acc = bE <= cE || exp((cE - bE) / T) > (double)(rnd() % 1000000) / 1e6;
        if (acc) { for (int i = 0; i < sz; i++) S[pos + i] = cand[bt][i]; retab_slot(k);
            c = cs[bt]; cE = bE; memcpy(UNC, ULIST[bt], sizeof(i64) * UN[bt]); NUNC = UN[bt]; }
        else { for (int i = 0; i < sz; i++) S[pos + i] = keep[i]; retab_slot(k); }
        steps++;
        if (c < best) { best = c; memcpy(bestS, S, sizeof(el) * d); lastimp = steps; write_sol(bestfile, bestS); }
        T = TMAX * pow(0.5, (steps - heat) / COOLSTEPS); if (T < TMIN) T = TMIN;
        if (steps - lastimp > REHEATSTEPS) {
            heat = steps; T = TMAX; memcpy(S, bestS, sizeof(el) * d); for (int u = 0; u < d; u++) make_tables(u);
            c = cost_sd(NOBOUND, UNC, UCAP, &NUNC); evals++; cE = (double)c / 2.0; lastimp = steps;
            fprintf(stderr, "reheat at step %lld: back to best S, cost %lld\n", (long long)steps, (long long)c);
        }
        if (steps % 200 == 0) fprintf(stderr, "t=%.0f step=%lld evals=%lld slot=%d cur=%lld best=%lld T=%.2f\n", now() - t0,
            (long long)steps, (long long)evals, k, (long long)c, (long long)best, T);
    }
    printf("RESULT SD d=%d D=%d group=%s x Z_%lld N=%lld vertices=%lld best=%lld evals=%lld steps=%lld time=%.1f slots=%d mu=%.2f\n",
           d, D, SPEC, (long long)NC, (long long)NG, (long long)(2 * NG), (long long)best, (long long)evals, (long long)steps, now() - t0, NSLOT - 1, mu);
    if (best == 0) {
        memcpy(S, bestS, sizeof(el) * d); for (int u = 0; u < d; u++) make_tables(u);
        int nu; i64 c2 = cost_sd(NOBOUND, UNC, UCAP, &nu);
        printf("re-evaluation of the best S: sd_cost %lld\n", (long long)c2);
        if (c2 == 0) { write_sol(out, bestS); printf("wrote %s\n", out); }
        return c2 == 0 ? 0 : 1;
    }
    return 1;
}
