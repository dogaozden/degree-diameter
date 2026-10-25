"""c7: lscreen.py with export_table read from the cache written by precompute.py (same filters, same lanneal call
with K = 8 and --secs as given, same TSV in $OUTDIR); the GAP calls that only count groups per order are answered
from the cache too. Usage (from the smallfam folder): python3 fastscreen.py BASE 7 17 25 --secs 3 --abmin 1 --abmax 1000000"""
import glob
import os
import runpy
import shutil
import sys
SMALLFAM = '/home/user/degree-diameter/research/theorems/smallfam'
sys.path.insert(0, SMALLFAM)
import allgroups  # noqa: E402
import screen  # noqa: E402
from allgroups import SP  # noqa: E402
CACHE = os.path.join(os.environ['SCRATCH'], 'cache')
NR = {}
for f in glob.glob(os.path.join(CACHE, '*.tab')):
    n = int(os.path.basename(f).split('_')[0]); NR[n] = NR.get(n, 0) + 1
_gap = allgroups.gap


def cached_gap(script, timeout):
    s = script.strip()
    if s.startswith('Print(NrSmallGroups(') and s.endswith('QUIT;'):
        n = int(s[len('Print(NrSmallGroups('):].split(')')[0])
        if n in NR:
            return f'{NR[n]}\n'
    return _gap(script, timeout)


def cached_export_table(n, i, timeout=1200):
    base = os.path.join(CACHE, f'{n}_{i}')
    tab = os.path.join(SP, f'scr_tab_{n}_{i}_{os.getpid()}.txt')
    shutil.copyfile(base + '.tab', tab)
    with open(base + '.struct') as f:
        return f.read().strip(), tab


allgroups.gap = cached_gap        # lscreen does "from allgroups import gap": it gets this one
screen.export_table = cached_export_table
sys.argv = ['lscreen.py'] + sys.argv[1:]
runpy.run_path(os.path.join(SMALLFAM, 'lscreen.py'), run_name='__main__')
