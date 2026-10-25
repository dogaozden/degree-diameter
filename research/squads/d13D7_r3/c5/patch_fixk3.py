p='/home/user/degree-diameter/research/squads/d13D7_r3/c5/red.c'
s=open(p).read()
old='''            if (bt < 0) {                     /* no admissible swap: kick by dropping one line, then regrow */
                npert++;
                int s0 = Kl[rndint(nK)];
                remK(s0); tabuIn[s0] = iter + TT;
            } else {'''
new='''            if (bt < 0) {                     /* no admissible swap: random swap ignoring tabu, else restore the best */
                npert++;
                int cand[NLN], nc = 0;
                for (int t = 0; t < NLN; t++) if (!inK[t] && lc[t] == 1) cand[nc++] = t;
                if (nc > 0) {
                    int t = cand[rndint(nc)], sv = -1;
                    for (int i = 0; i < nK; i++) if (conflict(t, Kl[i])) { sv = Kl[i]; break; }
                    remK(sv); addK(t); tabuIn[sv] = iter + TT; tabuOut[t] = iter + 2 * TT;
                } else {
                    while (nK > 0) remK(Kl[nK - 1]);
                    for (int i = 0; i < bestK_n; i++) addK(bestK[i]);
                }
            } else {'''
assert s.count(old)==1
s=s.replace(old,new)
open(p,'w').write(s)
print('patched3')
