p='/home/user/degree-diameter/research/squads/d13D7_r3/c5/red.c'
s=open(p).read()
start=s.index('        if (fixk > 0) {                       /* fixed-size mode')
end=s.index('        /* enumerate moves, keep the best admissible (ties random) */')
new='''        if (fixk > 0 && nK >= fixk) {         /* fixed-size mode (|K| = fixk): SWAP moves only */
            while (nK > fixk) { int r = Kl[rndint(nK)]; remK(r); tabuIn[r] = iter + TT; }
            int bd = -1000000, nbb = 0, bt = -1, bsw = -1;
            for (int t = 0; t < NLN; t++) {
                if (inK[t] || lc[t] != 1) continue;
                int sv = -1;
                for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { sv = Kl[i]; break; }
                int d = deltaSwap(sv, t);
                int adm = (tabuIn[t] <= iter && tabuOut[sv] <= iter) || (mopen + d > bestf - 11 * fixk);
                if (!adm) continue;
                if (d > bd) { bd = d; nbb = 1; bt = t; bsw = sv; }
                else if (d == bd && rndint(++nbb) == 0) { bt = t; bsw = sv; }
            }
            if (bt < 0) {                     /* no admissible swap: kick by dropping one line, then regrow */
                npert++;
                int s0 = Kl[rndint(nK)];
                remK(s0); tabuIn[s0] = iter + TT;
            } else {
                remK(bsw); addK(bt); nswap++;
                tabuIn[bsw] = iter + TT + rndint(TT); tabuOut[bt] = iter + 2 * TT;
            }
            if (nK == fixk) {
                int mm = mopen;
                if (11 * nK + mm > bestf) {
                    bestf = 11 * nK + mm; bestK_n = nK; memcpy(bestK, Kl, sizeof(int) * nK); lastImp = iter;
                    int32_t pp[16000]; int nn = 0;
                    if (build_points(pp, &nn) == 0) write_idx(argv[3], pp, nn, "best so far (fixed k)");
                    fprintf(stderr, "[%.1fs] it %ld: fixed-k %d: new best f=%d (m=%d)\\n", cpu(), iter, fixk, bestf, mm);
                }
            }
            if ((iter & 65535) == 0) fprintf(stderr, "[%.0fs] fixed-k %d it %ld m=%d best=%d swaps=%ld kicks=%ld\\n", cpu(), fixk, iter, mopen, bestf, nswap, npert);
            continue;
        }
'''
s=s[:start]+new+s[end:]
open(p,'w').write(s)
print('patched')
