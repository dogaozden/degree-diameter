import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4/c8')
import relax, lns, numpy as np
S0 = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S0['F']; sig = S0['sig']; H = S0['hubadj']
print('F', F, flush=True)
print('collinear with 65 (freed):', [(i, F[i]) for i in range(len(F)) if i != 3 and lns.PM[65][F[i]]], flush=True)
print('collinear pairs among F:', [(F[a], F[b]) for a in range(10) for b in range(a+1, 10) if lns.PM[F[a]][F[b]]], flush=True)
print('concurrent pairs among F lines:', [(a, b) for a in range(10) for b in range(a+1, 10) if lns.LM[sig[F[a]]][sig[F[b]]]], flush=True)
print('full cover cost', lns.cover(F, sig, H), flush=True)
Sl = relax.linear_S(F, sig)
print('linear S size', len(Sl), flush=True)
c, unc = relax.cover_sub(F, sig, H, [(i, s) for i in range(10) for s in (0, 1)])
print('check cover_sub all', c, unc, flush=True)
