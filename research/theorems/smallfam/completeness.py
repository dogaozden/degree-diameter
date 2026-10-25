"""Per order: number of distinct group ids handled in a run file vs NrSmallGroups(n).  Usage: python3 completeness.py TSV..."""
import subprocess, sys
from collections import defaultdict
def nr(ns):
    out = subprocess.run(['gap', '-q'], input='Print(List([' + ','.join(map(str, ns)) + '], NrSmallGroups), "\\n"); QUIT;\n',
                         capture_output=True, text=True).stdout
    return [int(x) for x in out.replace('[', ' ').replace(']', ' ').replace(',', ' ').split()]
for f in sys.argv[1:]:
    ids = defaultdict(set); skipped = set()
    for l in open(f):
        r = l.rstrip('\n').split('\t')
        if len(r) < 6 or not r[0].isdigit(): continue
        if r[1] == '*': skipped.add(int(r[0])); continue
        ids[int(r[0])].add(int(r[1]))
    ns = sorted(set(ids) | skipped)
    nq = [n for n in ns if n not in skipped]      # skipped orders may be missing from the library
    counts = dict(zip(nq, nr(nq)))
    incomplete = [(n, len(ids[n]), counts[n]) for n in ns if n not in skipped and len(ids[n]) != counts[n]]
    print(f'{f}: orders {ns[0]}..{ns[-1]} ({len(ns)} orders); skipped orders: {sorted(skipped)}; incomplete (order, done, total): {incomplete}')
