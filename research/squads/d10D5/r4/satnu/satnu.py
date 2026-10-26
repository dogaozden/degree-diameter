#!/usr/bin/env python3
"""satnu.py STATE.sol C0.lift2.sol "FDSET" OUT.lift2.sol: the coset-0 problem with sigma (and so every route, hub routes
included) fixed, as SAT with native XOR (CryptoMiniSat): variables nu_f; per unrouted opposite pair, one XOR variable per
valid geodesic (p_g = xor of its 4 flags) and not-all-equal clauses OR(p_g), OR(not p_g).  Coverage and D1 do not
depend on nu.  Writes OUT (sigma unchanged, new nu) if satisfiable.  env: SECS (time limit), THREADS."""
import sys, os, time
R4 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
st, c0, fds, out = [os.path.abspath(x) if i != 2 else x for i, x in enumerate(sys.argv[1:5])]
os.chdir(R4); sys.path.insert(0, R4)
sys.argv = ['lns3.py', st, c0, fds, out]; os.environ['SECS'] = '0'
exec(open('lns3.py').read().split("best = cur; t0 = time.time()")[0])
import pycryptosat
bp, bl, rp, rl = bad_ids(sig)
s = pycryptosat.Solver(threads=int(os.environ.get('THREADS', 1)), verbose=int(os.environ.get('VERB', 0)))
nxt = [N * 8 + 1]
def new():
    v = nxt[0]; nxt[0] += 1; return v
npair = 0; nx = 0
for Fl, Vl, routed in ((PF, PV, rp), (LF, LV, rl)):
    for q in np.nonzero(~routed)[0]:
        ps = []
        for g in range(8):
            if not Vl[q, g]: continue
            v = new(); s.add_xor_clause([v] + [int(f) + 1 for f in Fl[q, g]], False); ps.append(v); nx += 1
        s.add_clause(ps); s.add_clause([-v for v in ps]); npair += 1
print('pairs', npair, 'xor clauses', nx, 'vars', nxt[0] - 1, flush=True)
t0 = time.time(); sat, sol = s.solve(); print('result', sat, '%.0fs' % (time.time() - t0), flush=True)
if sat:
    for f in range(N * 8): nu[f] = 1 if sol[f + 1] else 0
    set_unmixed(nu); cur = total(sig)[0]; print('exact after SAT:', total(sig), flush=True)
    write(sig)
