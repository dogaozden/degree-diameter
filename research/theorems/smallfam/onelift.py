"""Exhaustive lift search over ONE SmallGroup(n, i) and one base (the per-group step of allgroups.py --base):
first free voltage over Aut(G)-orbit representatives, the other free voltages over all of G (lx.c).
Usage: SCRATCH=dir python3 onelift.py n i BASE D [--threads T]"""
import argparse, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from allgroups import export  # noqa: E402
ap = argparse.ArgumentParser()
ap.add_argument('n', type=int); ap.add_argument('i', type=int); ap.add_argument('base'); ap.add_argument('D', type=int)
ap.add_argument('--threads', type=int, default=1)
ap.add_argument('--identity-only', action='store_true', help='plan = the identity only (completes a run whose plan skipped it)')
a = ap.parse_args()
struct, tab, plan, qmap = export(a.n, a.i, True, 3600, single=True)
if a.identity_only:
    e = open(tab).readline().split()[1]
    open(plan, 'w').write(e + '\n')
print(f'# lift of {a.base} over SmallGroup({a.n},{a.i}) = {struct}; plan lines {sum(1 for _ in open(plan))}; D={a.D}', flush=True)
r = subprocess.run([os.path.join(HERE, 'lx'), 'tab', tab, a.base, str(a.D), plan, '50'], capture_output=True, text=True,
                   env=dict(os.environ, THREADS=str(a.threads)))
print(r.stdout, end='', flush=True)
for p in (tab, plan, qmap):
    os.remove(p)
