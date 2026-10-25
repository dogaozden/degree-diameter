"""Consistency check: hx (exhaustive) says SmallGroup(432,30) and (432,31) have no (4,7) Haar graph and (432,247),
(432,249) do.  Run the independent annealer hanneal (60 s, 2 seeds) on each and record its best cost."""
import os, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from screen import export_table
HERE = os.path.dirname(os.path.abspath(__file__))
out = open(os.path.join(HERE, 'runs', 'hx_vs_hanneal_d4D7.txt'), 'w')
for gid in (30, 31, 247, 249):
    struct, tab = export_table(432, gid)
    for s in (1, 2):
        r = subprocess.run([os.path.join(HERE, 'hanneal'), tab, '4', '7', '60', str(s), '8', tab + '.sol'],
                           capture_output=True, text=True).stdout.strip().splitlines()[-1]
        out.write(f'SmallGroup(432,{gid}) {struct} seed {s}: {r}\n'); out.flush()
    os.remove(tab)
