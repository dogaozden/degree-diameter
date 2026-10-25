p='/home/user/degree-diameter/research/squads/d13D7_r3/c5/red.c'
s=open(p).read()
reps=[
('''                int adm = (tabuIn[t] <= iter && tabuOut[sv] <= iter) || (mopen + d > bestf - 11 * fixk);''',
 '''                int adm = (tabuIn[t] <= iter && tabuOut[sv] <= iter) || (mopen + d > bestm_fix);'''),
('''                if (11 * nK + mm > bestf) {
                    bestf = 11 * nK + mm; bestK_n = nK; memcpy(bestK, Kl, sizeof(int) * nK); lastImp = iter;
                    int32_t pp[16000]; int nn = 0;
                    if (build_points(pp, &nn) == 0) write_idx(argv[3], pp, nn, "best so far (fixed k)");
                    fprintf(stderr, "[%.1fs] it %ld: fixed-k %d: new best f=%d (m=%d)\\n", cpu(), iter, fixk, bestf, mm);
                }''',
 '''                if (mm > bestm_fix) {
                    bestm_fix = mm; bestf = 11 * nK + mm; bestK_n = nK; memcpy(bestK, Kl, sizeof(int) * nK); lastImp = iter;
                    int32_t pp[16000]; int nn = 0;
                    if (build_points(pp, &nn) == 0) write_idx(argv[3], pp, nn, "best so far (fixed k)");
                    fprintf(stderr, "[%.1fs] it %ld: fixed-k %d: new best m=%d (f=%d)\\n", cpu(), iter, fixk, mm, bestf);
                }'''),
('''        if (fixk > 0 && nK >= fixk) {         /* fixed-size mode (|K| = fixk): SWAP moves only */''',
 '''        if (fixk > 0 && nK >= fixk) {         /* fixed-size mode (|K| = fixk): SWAP moves only */
            static int bestm_init = 0; if (!bestm_init) { bestm_init = 1; bestm_fix = -1; }'''),
('''static long tabuIn[NLN], tabuOut[NLN];''','''static long tabuIn[NLN], tabuOut[NLN];
static int bestm_fix = -1;'''),
]
for a,b in reps:
    n=s.count(a)
    assert n==1, (n, a[:70])
    s=s.replace(a,b)
open(p,'w').write(s)
print('patched2')
