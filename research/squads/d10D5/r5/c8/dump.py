#!/usr/bin/env python3
# dump.py STATE.sol C0.lift2.sol "FDSET": builds lns3's geodesic tables (exec of lns3 top part, nothing searched) and
# writes c8/tab.bin for the exact flip-tree search (flip.c). Layout (int32 LE): M, N3(=3200), then per pair i:
# 32 flags (geodesic g, flag k at 8*g+k? no: flags[g*4+k]), 8 valid flags, active(0/1); then nu[3200] (0/1).
import sys, os
R4 = '/home/user/degree-diameter/research/squads/d10D5/r4'
src = open(os.path.join(R4, 'lns3.py')).read()
top = src.split("\nsecs = float(os.environ.get('SECS'")[0]
A = [os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2]), sys.argv[3]]; os.chdir(R4); sys.path.insert(0, R4); sys.argv = ["lns3.py"] + A + ["/dev/null"]
g = {'__name__': 'lns3top', '__file__': os.path.join(R4, 'lns3.py')}
exec(compile(top, 'lns3top', 'exec'), g)
import numpy as np
N = g['N']; PF, PV, LF, LV = g['PF'], g['PV'], g['LF'], g['LV']; PA, PB, LA, LB = g['PA'], g['PB'], g['LA'], g['LB']
sig, isfree, LM, PM, nu = g['sig'], g['isfree'], g['LM'], g['PM'], g['nu']
sinv = np.empty(N, np.int64); sinv[sig] = np.arange(N); nf = ~isfree
rP = LM[sig[PA], sig[PB]] & nf[PA] & nf[PB]          # routed points pairs
rL = PM[sinv[LA], sinv[LB]] & nf[sinv[LA]] & nf[sinv[LB]]
Fall = np.concatenate([PF, LF]).astype(np.int32); Vall = np.concatenate([PV, LV]).astype(np.int32)
act = np.concatenate([~rP, ~rL]).astype(np.int32)
M = len(Fall)
with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tab.bin'), 'wb') as f:
    np.array([M, 3200], np.int32).tofile(f)
    rec = np.concatenate([Fall.reshape(M, 32), Vall.reshape(M, 8), act.reshape(M, 1)], 1).astype(np.int32)
    rec.tofile(f)
    nu.astype(np.int32).tofile(f)
unm = np.concatenate([g['UPv'], g['ULv']]) & (act == 1)
print('pairs', M, 'active', int(act.sum()), 'nu ones', int(nu.sum()), 'bad (unmixed unrouted)', int(unm.sum()), flush=True)
