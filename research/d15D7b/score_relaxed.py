#!/usr/bin/env python3
"""score_relaxed.py: exact scorer for the relaxed (15,7) construction. Given the four bottleneck friendly sets
(P0: points freed at 0->2, P1: points at 1->2, S3: lines at 2->3, S4: lines at 2->4; each may contain pairs, every
element at most one partner), it designs the non-bottleneck friendly sets to cover the partners (design_cover.py, then design3.py:
private covers),
assigns hub slots with the pair conditions (tm3_build.py assign), drops one end of every pair that cannot be served
(v3_drop.py) and prints the resulting hub counts and n = 14*177,156 + KB + KA. Writes everything into WORKDIR
(spec.txt, the set files, assign.sol = a typedmirror3 solution without hub graph; v3_hub.sh then adds the hub graph).
usage: score_relaxed.py HEXBIN MIRROR_SOL BASEDIR P0.txt P1.txt S3.txt S4.txt WORKDIR
  BASEDIR holds RH.txt, RHb.txt, RL.txt, RLb.txt (master's sets and collineation images)"""
import sys, os, shutil, subprocess
import numpy as np
D = os.path.dirname(os.path.abspath(__file__))
hexfn, mirfn, based, p0, p1, s3, s4, wd = sys.argv[1:9]
hexfn = os.path.abspath(hexfn); mirfn = os.path.abspath(mirfn)
os.makedirs(wd, exist_ok=True)
for f in ('RH.txt', 'RHb.txt', 'RL.txt', 'RLb.txt'): shutil.copy(os.path.join(based, f), os.path.join(wd, f))
for src, dst in ((p0, 'P0.txt'), (p1, 'P1.txt'), (s3, 'S3.txt'), (s4, 'S4.txt')): shutil.copy(src, os.path.join(wd, dst))
shutil.copy(mirfn, os.path.join(wd, os.path.basename(mirfn)))
def run(*a):
    r = subprocess.run([sys.executable] + list(a), capture_output=True, text=True, cwd=wd)
    if r.returncode not in (0,): sys.exit(f'failed: {a}\n{r.stdout}\n{r.stderr}')
    return r.stdout
for f, m in (('P0', 'P'), ('P1', 'P'), ('S3', 'L'), ('S4', 'L')): run(os.path.join(D, 'paired.py'), hexfn, m, f + '.txt', f + '.paired')
print(run(os.path.join(D, 'design_cover.py'), hexfn, 'L', 'P0.paired', 'RL.txt', '1', 'D50.txt'), end='')
print(run(os.path.join(D, 'design_cover.py'), hexfn, 'L', 'P1.paired', 'RLb.txt', '2', 'D61.txt'), end='')
print(run(os.path.join(D, 'design_cover.py'), hexfn, 'P', 'S3.paired', 'RH.txt', '3', 'D35.txt'), end='')
print(run(os.path.join(D, 'design_cover.py'), hexfn, 'P', 'S4.paired', 'RHb.txt', '4', 'D46.txt'), end='')
# private covers (design3.py, squad c157b-r2 card c4): every partner gets its own covering element, no covering element
# holds two needed elements (the joining element of a pair is never used), so no two demands compete for one slot
for f, mode, need in (('D50', 'L', 'P0.paired'), ('D61', 'L', 'P1.paired'), ('D35', 'P', 'S3.paired'), ('D46', 'P', 'S4.paired')):
    print(run(os.path.join(D, 'design3.py'), hexfn, mode, need, f + '.txt', '7', '300', f + '.txt.3'), end='')
    shutil.move(os.path.join(wd, f + '.txt.3'), os.path.join(wd, f + '.txt'))
open(os.path.join(wd, 'spec.txt'), 'w').write('0 2 P0.txt\n1 1 P1.txt\n2 1 S3.txt\n2 2 S4.txt\n3 2 D35.txt\n3 3 RHb.txt\n'
                                             '4 1 RH.txt\n4 2 D46.txt\n5 2 D50.txt\n6 1 RLb.txt\n5 3 RL.txt\n6 2 D61.txt\n')
out = run(os.path.join(D, 'v3_drop.py'), hexfn, os.path.basename(mirfn), 'spec.txt', '1', 'assign.sol')
last = [l for l in out.split('\n') if l.startswith('free A-slots')][-1]
KB, KA = (int(v) for v in last.split('-> hubs')[1].split())
drops = sum(int(l.split()[1]) for l in out.split('\n') if l.strip().startswith('dropped'))
sizes = [len(np.loadtxt(os.path.join(wd, f), dtype=np.int64).reshape(-1)) for f in ('P0.txt', 'P1.txt', 'S3.txt', 'S4.txt')]
print(f'dropped {drops} elements; final sets P0 {sizes[0]} P1 {sizes[1]} S3 {sizes[2]} S4 {sizes[3]}')
print(f'SCORE n = {14 * 177156 + KB + KA} (hubs {KB} + {KA}); hub graph still to be added (v3_hub.sh)')
