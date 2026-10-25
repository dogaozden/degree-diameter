p='/home/user/degree-diameter/research/squads/d13D7_r3/c5/red.c'
s=open(p).read()
old='''            int bd = -1000000, nbb = 0, bt = -1, bsw = -1;
            for (int t = 0; t < NLN; t++) {
                if (inK[t] || lc[t] != 1) continue;
                int sv = -1;
                for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { sv = Kl[i]; break; }
                int d = deltaSwap(sv, t);
                int adm = (tabuIn[t] <= iter && tabuOut[sv] <= iter) || (mopen + d > bestm_fix);
                if (!adm) continue;
                if (d > bd) { bd = d; nbb = 1; bt = t; bsw = sv; }
                else if (d == bd && rndint(++nbb) == 0) { bt = t; bsw = sv; }
            }'''
new='''            int bd = -1000000, nbb = 0, bt = -1, bsw = -1;
            for (int t = 0; t < NLN; t++) {
                if (inK[t] || lc[t] > 1) continue;
                for (int i = 0; i < nK; i++) {
                    int sv = Kl[i];
                    if (lc[t] == 1 && !conflict(t, sv)) continue;   /* t's only conflict must leave */
                    int d = deltaSwap(sv, t);
                    int adm = (tabuIn[t] <= iter && tabuOut[sv] <= iter) || (mopen + d > bestm_fix);
                    if (!adm) continue;
                    if (d > bd) { bd = d; nbb = 1; bt = t; bsw = sv; }
                    else if (d == bd && rndint(++nbb) == 0) { bt = t; bsw = sv; }
                }
            }'''
assert s.count(old)==1
s=s.replace(old,new)
old2='''                int cand[NLN], nc = 0;
                for (int t = 0; t < NLN; t++) if (!inK[t] && lc[t] == 1) cand[nc++] = t;
                if (nc > 0) {
                    int t = cand[rndint(nc)], sv = -1;
                    for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { sv = Kl[i]; break; }
                    remK(sv); addK(t); tabuIn[sv] = iter + TT; tabuOut[t] = iter + 2 * TT;'''
new2='''                int cand[NLN], nc = 0;
                for (int t = 0; t < NLN; t++) if (!inK[t] && lc[t] <= 1) cand[nc++] = t;
                if (nc > 0) {
                    int t = cand[rndint(nc)], sv = -1;
                    if (lc[t] == 1) { for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { sv = Kl[i]; break; } }
                    else sv = Kl[rndint(nK)];
                    remK(sv); addK(t); tabuIn[sv] = iter + TT; tabuOut[t] = iter + 2 * TT;'''
assert s.count(old2)==1
s=s.replace(old2,new2)
open(p,'w').write(s)
print('patched4')
