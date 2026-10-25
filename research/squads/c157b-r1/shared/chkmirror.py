#!/usr/bin/env python3
"""chkmirror.py: scorer for mirrored sets (card c7). R' = point ids (Rp.txt style), sigma = a bijection points -> lines
(N ids, line i = sigma(point i)). Checks (N1) R' non-collinear, (N2) sigma(R') non-concurrent, (L) sigma(Gamma_2(x)) =
Gamma_2(sigma(x)) for every x in R' (Gamma_2(x) = the 132 points collinear with x, Gamma_2(l) = the 132 lines meeting l).
usage: python3 chkmirror.py RP.txt SIGMA.txt      prints 'VALID m <|R'|>' or 'INVALID ...'"""
import sys, os, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
b = open(os.path.join(HERE, 'hex_q11.bin'), 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
PL = flat_l[np.lexsort((flat_l, flat_p))].reshape(N, Q1)
Rp = np.loadtxt(sys.argv[1], dtype=np.int64).reshape(-1); sig = np.loadtxt(sys.argv[2], dtype=np.int64).reshape(-1)
if len(sig) != N or len(np.unique(sig)) != N or sig.min() < 0 or sig.max() >= N: print('INVALID sigma is not a bijection'); sys.exit(1)
if len(np.unique(Rp)) != len(Rp): print('INVALID repeated ids'); sys.exit(1)
inRp = np.zeros(N, bool); inRp[Rp] = True; inSR = np.zeros(N, bool); inSR[sig[Rp]] = True
if (inRp[LP].sum(1) > 1).any(): print("INVALID R' collinear"); sys.exit(1)
if (inSR[PL].sum(1) > 1).any(): print("INVALID sigma(R') concurrent"); sys.exit(1)
for x in Rp:
    G2x = np.setdiff1d(LP[PL[x]].reshape(-1), [x]); l = sig[x]
    G2l = np.setdiff1d(PL[LP[l]].reshape(-1), [l])
    if not np.array_equal(np.sort(sig[G2x]), G2l): print('INVALID local duality fails at', x); sys.exit(1)
print(f'VALID m {len(Rp)}')
