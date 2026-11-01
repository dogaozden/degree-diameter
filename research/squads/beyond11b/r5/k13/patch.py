import sys
src = open('/home/user/degree-diameter/research/squads/beyond11b/tools/haar_gen3s.c').read()
def rep(old, new):
    global src
    assert src.count(old) == 1, old[:60]
    src = src.replace(old, new)
rep("uint32_t *cf, *ci; long long lev[64]; } ctx;", "uint32_t *cf, *ci, *cf2, *ci2; long long lev[64]; } ctx;")
rep("c->cf = malloc(4 * (size_t)R); c->ci = malloc(4 * (size_t)R);",
    "c->cf = malloc(4 * (size_t)R); c->ci = malloc(4 * (size_t)R); c->cf2 = malloc(4 * (size_t)R); c->ci2 = malloc(4 * (size_t)R);")
rep("static int walk(int g, int *side, int len, int avoid) {",
"""static int PAIRP = 0, LOCALP = 0, LOCALW = 3;      /* k13 moves: PAIRP % two generators replaced at once, LOCALP % s -> s*w */
static long long acc_mt[3], prop_mt[3];
static int localmove(int i) {   /* new generator S[i]*w, w a random word of length 1..LOCALW in S_j^{+-1}, j >= 1 */
    int w = ident, len = 1 + (int)(rnd() % LOCALW);
    for (int k = 0; k < len; k++) { int j = 1 + (int)(rnd() % (d - 1)); w = gmul(w, (rnd() & 1) ? S[j] : SI[j]); }
    return gmul(S[i], w);
}
static int walk(int g, int *side, int len, int avoid) {""")
rep("int xs[256]; long long cs[256]; double ce[256];", "int xs[256], ys[256]; long long cs[256]; double ce[256];")
rep("""        int i = 1 + rnd() % (d - 1);
        for (int t = 0; t < K; t++) {
            int x = ((int)(rnd() % 100) < TARGP) ? targeted(i) : -1;
            if (x < 0 || x == ident || used(x, i)) do x = rnd() % N; while (x == ident || used(x, i));
            xs[t] = x;
        }""",
"""        int i = 1 + rnd() % (d - 1), i2 = -1, mt = 0;
        { int ru = (int)(rnd() % 100);
          if (ru < PAIRP && d >= 3) { mt = 1; do i2 = 1 + rnd() % (d - 1); while (i2 == i); }
          else if (ru < PAIRP + LOCALP) mt = 2; }
        for (int t = 0; t < K; t++) {
            int x = -1, y = -1;
            if (mt == 2) { x = localmove(i); if (x == ident || x == S[i] || used(x, i)) x = -1; }
            else if ((int)(rnd() % 100) < TARGP) x = targeted(i);
            if (x < 0 || x == ident || used(x, i)) do x = rnd() % N; while (x == ident || used(x, i));
            if (mt == 1) { do y = rnd() % N; while (y == ident || y == x || used(y, i2)); }
            xs[t] = x; ys[t] = y;
        }""")
rep("""            tf[i] = cx->cf; ti[i] = cx->ci;
""", """            tf[i] = cx->cf; ti[i] = cx->ci;
            if (mt == 1) { make_tables(ys[t], cx->cf2, cx->ci2); tf[i2] = cx->cf2; ti[i2] = cx->ci2; }
""")
rep("""        if (bE <= cE || exp((cE - bE) / T) > (rnd() % 1000000) / 1e6) {
            S[i] = bx; SI[i] = ginv(bx); make_tables(bx, TF[i], TI[i]); c = bc; cE = bE; collect_saved(SAVE[bt]);
        }""", """        prop_mt[mt]++;
        if (bE <= cE || exp((cE - bE) / T) > (rnd() % 1000000) / 1e6) {
            S[i] = bx; SI[i] = ginv(bx); make_tables(bx, TF[i], TI[i]);
            if (mt == 1) { int by = ys[bt]; S[i2] = by; SI[i2] = ginv(by); make_tables(by, TF[i2], TI[i2]); }
            acc_mt[mt]++; c = bc; cE = bE; collect_saved(SAVE[bt]);
        }""")
rep("""    int prof = getenv("PROFILE") ? atoi(getenv("PROFILE")) : 0;""",
"""    int prof = getenv("PROFILE") ? atoi(getenv("PROFILE")) : 0;
    PAIRP = getenv("PAIRP") ? atoi(getenv("PAIRP")) : 0; LOCALP = getenv("LOCALP") ? atoi(getenv("LOCALP")) : 0;
    LOCALW = getenv("LOCALW") ? atoi(getenv("LOCALW")) : 3; if (LOCALW < 1) LOCALW = 1;""")
rep("""    printf("RESULT d=%d D=%d group""", """    fprintf(stderr, "moves accepted/proposed: plain %lld/%lld pair %lld/%lld local %lld/%lld\\n", acc_mt[0], prop_mt[0], acc_mt[1], prop_mt[1], acc_mt[2], prop_mt[2]);
    printf("RESULT d=%d D=%d group""")
open('/home/user/degree-diameter/research/squads/beyond11b/r5/k13/hg.c', 'w').write(src)
print("ok")
