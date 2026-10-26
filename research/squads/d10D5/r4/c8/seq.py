import sys, time, json, random, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r4/c8')
import relax, lns, numpy as np
os.environ.setdefault('EXCL', '1')
S0 = lns.read_sol('/home/user/degree-diameter/research/squads/d10D5/r4/k10_orbit_100.sol')
F = S0['F']; sig = S0['sig']; H = S0['hubadj']
mode = sys.argv[1]; SECS = float(sys.argv[2]); steps_arg = sys.argv[3] if len(sys.argv) > 3 else 'all'
if mode == 'lin':
    S = relax.linear_S(F, sig)
else:
    size = int(mode)
    rng = random.Random(7)
    # S = points near the hole: preimages of lines through target 69, points of 65^perp, plus random linear fill
    isfree = np.zeros(lns.N, bool); isfree[F] = True
    sinv = np.empty(lns.N, np.int64); sinv[sig] = np.arange(lns.N)
    lin = set(relax.linear_S(F, sig))
    core = [int(sinv[L]) for L in lns.LOF[69] if int(sinv[L]) in lin] + [x for x in np.nonzero(lns.PM[65] & ~isfree)[0] if int(x) in lin]
    core = list(dict.fromkeys(int(x) for x in core))
    rest = [x for x in sorted(lin) if x not in set(core)]
    rng.shuffle(rest)
    S = (core + rest)[:size]
print('mode', mode, 'S size', len(S), flush=True)
steps = [(3, 0)]
steps += [(0, 0), (6, 0), (8, 0)]
steps += [(1, 0), (2, 0), (4, 0), (5, 0), (7, 0), (9, 0)]
steps += [(3, 1), (0, 1), (6, 1), (8, 1)]
steps += [(1, 1), (2, 1), (4, 1), (5, 1), (7, 1), (9, 1)]
if steps_arg != 'all': steps = steps[:int(steps_arg)]
cons = []
cur = sig.copy()
for st in steps:
    cons.append(st)
    new, info = relax.model(F, cur, H, S, cons, secs=SECS, workers=1, seed=1, hint=True)
    if new is None:
        print(json.dumps(dict(n=len(cons), added=st, **info)), flush=True); continue
    c, unc = relax.cover_sub(F, new, H, cons)
    print(json.dumps(dict(n=len(cons), added=st, exact_sub=c, unc=unc[:4], **info)), flush=True)
    cur = new
    if c == 0 and len(cons) == 20:
        lns.write_sol('/home/user/degree-diameter/research/squads/d10D5/r4/c8/full20.sol', S0, new, 0)
        print('FULL 20-pair cover 0 written', flush=True)
np.save('/home/user/degree-diameter/research/squads/d10D5/r4/c8/last_sig_%s.npy' % mode, cur)
print('done', flush=True)
