src = open('haar_big0.c').read()
helper_anchor = "/* ---------------- FIXF: screen candidates"
helper = r'''/* ---- h14 (r6): FIN = hole-directed generic finisher (single generators, sideways moves) ---- */
static int targeted_at(el *x, i64 hidx) {   /* as targeted(), but the walks end at the given hole */
    WINV = (hidx & BHOLE) != 0;
    el u = eofidx(hidx & ~BHOLE);
    for (int tries = 0; tries < 20; tries++) {
        int a = (int)(rnd() % (D - 1)), b = (int)(rnd() % (D - 1 - a));
        int sp = 0, sq = (D % 2 == 0);
        el Pp = walk(E_ID, &sp, a), Qv = walk(u, &sq, b);
        if (sp == sq) continue;
        el gA = sp == 0 ? Pp : Qv, hB = sp == 0 ? Qv : Pp;
        *x = emul(hB, einv(gA)); if (WINV) *x = einv(*x);
        WINV = 0; return 1;
    }
    WINV = 0; return 0;
}

'''
assert src.count(helper_anchor) == 1
src = src.replace(helper_anchor, helper + helper_anchor)

main_anchor = '    fprintf(stderr, "setup %.1fs\\n", now() - tset);\n'
assert src.count(main_anchor) == 1, src.count(main_anchor)
block = r'''    if (getenv("FIN")) {   /* h14 FIN: START = any solution file (no orbit form); moves replace one generator */
        if (!getenv("START") || !read_sol(getenv("START"), S)) { fprintf(stderr, "FIN needs START=solution\n"); return 2; }
        for (int u = 0; u < d; u++) for (int v = 0; v < u; v++) if (eeq(S[u], S[v])) { fprintf(stderr, "repeated generator\n"); return 2; }
        int tpf = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
        int fK = K > 64 ? 64 : K; double tf0 = now(); long fev = 1; int rounds = 0;
        for (int u = 0; u < d; u++) make_tables(u);
        i64 cur = cost(NOBOUND, UNC, UCAP, &NUNC), gbest = cur;
        fprintf(stderr, "FIN start cost %lld N %lld K %d TARGP %d\n", (long long)cur, (long long)NG, fK, tpf);
        char bfin[1024]; snprintf(bfin, sizeof bfin, "%s.best", out);
        while (cur > 0 && !stop_flag && now() - tf0 < secs) {
            rounds++;
            int i = 1 + (int)(rnd() % (d - 1));
            el old = S[i], bc = old, cand[64]; i64 bcost = -1;
            i64 hid = NUNC > 0 ? UNC[rnd() % NUNC] : 0;
            AVOID = 1ULL << i;
            for (int c = 0; c < fK; c++) {   /* candidates: forced through one hole (targeted), else random */
                el x; int ok = 0;
                for (int tr = 0; tr < 1000 && !ok; tr++) {
                    if (NUNC > 0 && (int)(rnd() % 100) < tpf && targeted_at(&x, hid)) { }
                    else x = randel();
                    ok = !eeq(x, E_ID);
                    for (int u = 0; u < d && ok; u++) if (u != i && eeq(S[u], x)) ok = 0;
                }
                cand[c] = x;
            }
            AVOID = 0;
            for (int c = 0; c < fK; c++) {
                S[i] = cand[c]; make_tables(i);
                i64 bound = bcost < 0 ? NOBOUND : bcost + 1, r;   /* ties allowed (sideways) */
                int nu = 0; r = cost(bound, ULIST[0], UCAP, &nu); fev++;
                if (r < 0) continue;
                if (bcost < 0 || r < bcost || (r == bcost && (rnd() & 1))) { bcost = r; bc = cand[c]; }
                if (r == 0) break;
            }
            if (bcost <= cur) { S[i] = bc; cur = bcost; } else S[i] = old;
            make_tables(i);
            cur = cost(NOBOUND, UNC, UCAP, &NUNC); fev++;   /* exact cost and uncovered list of the new state */
            if (cur < gbest) { gbest = cur; write_sol(bfin, S); }
            write_sol(out, S);
            fprintf(stderr, "round %d slot %d: min cand %lld cur %lld best %lld evals %ld NUNC %lld t=%.1f\n", rounds, i,
                    (long long)bcost, (long long)cur, (long long)gbest, fev, (long long)NUNC, now() - tf0);
        }
        if (cur == 0) {
            printf("RESULT FIN cost0 d=%d D=%d group=%s x Z_%lld N=%lld vertices=%lld evals=%ld time=%.1f file=%s\n", d, D, SPEC, (long long)NC, (long long)NG, (long long)(2 * NG), fev, now() - tf0, out);
            return 0;
        }
        printf("RESULT FIN open d=%d D=%d group=%s x Z_%lld N=%lld cur=%lld best=%lld evals=%ld rounds=%d time=%.1f\n", d, D, SPEC, (long long)NC, (long long)NG, (long long)cur, (long long)gbest, fev, rounds, now() - tf0);
        return 0;
    }
'''
src = src.replace(main_anchor, main_anchor + block)
open('haar_fin.c', 'w').write(src)
print('ok')
