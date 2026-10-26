import sys; sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4'); import lns
import numpy as np
fn = sys.argv[1]; S = lns.read_sol(fn); F = S['F']; sig = S['sig']; A = S['hubadj'].copy()
H = S['H']; k = len(F)
c0, unc = lns.cover(F, sig, A, listing=True); print('base cover', c0, unc)
hole = unc[0]; i, side, t = hole
print('freed', F); print('lines of freed', [int(sig[p]) for p in F])
# lines through t that are freed lines
J = [j for j in range(k) if t in lns.PTS[sig[F[j]]]]
print('target', t, 'on freed lines of flags', J, 'lines of t', list(lns.LOF[t]))
rows = S['rows']; hg = [int(x) for x in rows['hubgraph']]
deg_line = np.zeros(k*H, int); deg_pt = np.zeros(k*H, int)
for e in range(0, len(hg), 2): deg_line[hg[e]] += 1; deg_pt[hg[e+1]] += 1
print('hub degs line', deg_line.reshape(k,H).tolist()); print('hub degs pt', deg_pt.reshape(k,H).tolist())
for j in J:
    for a in range(H):
        for b in range(H):
            B = A.copy(); B[i, j] = True
            c, _ = lns.cover(F, sig, B)
            ok = (deg_line[i*H+a] < 4) and (deg_pt[j*H+b] < 4) and not A[i,j]
            print('add pair line-hub', i*H+a, 'pt-hub', j*H+b, 'cover after', c, 'degree ok', ok, 'already', bool(A[i,j]))
