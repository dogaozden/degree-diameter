import sys
p = '/home/user/degree-diameter/research/squads/beyond11b/r3/i13/haar_gen3_lb.c'
s = open(p).read()


def rep(old, new, cnt=1):
    global s
    assert s.count(old) == cnt, (s.count(old), old[:60])
    s = s.replace(old, new)


glob = r'''
/* ---- i13: label-balanced generator sets for meta groups Z_m x| Z_k (n = 1). label(x) = x mod k (C_k coordinate).
 * LB=1 enables: (a) at least LBMIN distinct labels among the d elements, (b) max_{t=1..k-1} |phi_t|/d <= LBT,
 * phi_t = sum_s w^{t c_s}, w = exp(2 pi i/k). Candidates violating it are redrawn (cap 200000 tries, then accepted). */
static int LBON = 0, LBMIN = 3, LBK = 0; static double LBT = 0.7; static double LCS[64], LSN[64];
static long long LBFALL = 0, LBREJ = 0;
static int lbfull(int i, int x) {   /* S with S[i] replaced by x (i < 0: S as is) */
    if (!LBON) return 1;
    int cnt[64]; memset(cnt, 0, sizeof cnt);
    for (int s = 0; s < d; s++) { int y = (s == i) ? x : S[s]; cnt[y % LBK]++; }
    int dist = 0; for (int c = 0; c < LBK; c++) if (cnt[c]) dist++;
    if (dist < LBMIN) return 0;
    double mx = 0;
    for (int t = 1; t < LBK; t++) {
        double re = 0, im = 0;
        for (int c = 0; c < LBK; c++) if (cnt[c]) { int idx = (t * c) % LBK; re += cnt[c] * LCS[idx]; im += cnt[c] * LSN[idx]; }
        double v = sqrt(re * re + im * im) / d; if (v > mx) mx = v;
    }
    return mx <= LBT;
}
'''
rep('static int TWIST = 0, CSL = 0, top_level = 0;', glob + 'static int TWIST = 0, CSL = 0, top_level = 0;')

envblk = '''N = (int)NN; ident = Q->ident * ncyc;
    if (getenv("LB") && atoi(getenv("LB"))) {
        if (Q->type != G_META || ncyc != 1) { fprintf(stderr, "LB needs a meta group x Z_1\\n"); return 2; }
        LBON = 1; LBK = Q->k; LBT = getenv("LBT") ? atof(getenv("LBT")) : 0.7; LBMIN = getenv("LBMIN") ? atoi(getenv("LBMIN")) : 3;
        for (int c = 0; c < LBK; c++) { LCS[c] = cos(2 * M_PI * c / LBK); LSN[c] = sin(2 * M_PI * c / LBK); }
        fprintf(stderr, "LB on: k=%d LBT=%.3f LBMIN=%d\\n", LBK, LBT, LBMIN);
    }'''
rep('N = (int)NN; ident = Q->ident * ncyc;', envblk)

rep('    for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; }\n    for (int i = 0; i < d; i++) { SI[i]',
    '    for (int tries = 0; ; tries++) { for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; }\n        if (!LBON || lbfull(-1, 0) || tries > 2000000) break; }\n    for (int i = 0; i < d; i++) { SI[i]')

rep('''            if (x < 0 || x == ident || used(x, i)) do x = rnd() % N; while (x == ident || used(x, i));''',
'''            if (x < 0 || x == ident || used(x, i) || !lbfull(i, x)) {
                long long tr = 0;
                do { x = rnd() % N; tr++; if (LBON && x != ident && !used(x, i) && !lbfull(i, x)) LBREJ++; }
                while (x == ident || used(x, i) || (LBON && tr < 200000 && !lbfull(i, x)));
                if (LBON && !lbfull(i, x)) LBFALL++;
            }''')

rep('    printf("RESULT d=%d', '    if (LBON) fprintf(stderr, "LB: rejected draws %lld, fallbacks %lld\\n", LBREJ, LBFALL);\n    printf("RESULT d=%d')
open(p, 'w').write(s)
print("ok")
