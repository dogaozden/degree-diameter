#!/usr/bin/env python3
"""Per-order summary of the exact (5,5) searches from runs/*.txt (markdown table on stdout)."""
import glob, re, subprocess
def load(prog):
    d = {}
    for f in glob.glob(f'runs/{prog}_[0-9]*.txt'):
        o = int(re.search(r'_(\d+)\.txt$', f).group(1))
        for ln in open(f):
            if ' :: ' not in ln: continue
            head, res = ln.split(' :: ', 1); i = int(head.split()[1])
            m = re.search(r'solutions (\d+)', res); s = int(m.group(1)) if m else None
            d.setdefault(o, {})[i] = s
    return d
a1, a2, hx = load('b4a1x'), load('b4a2y'), load('haar5x')
prev = {89: 1, 90: 10, 91: 1, 92: 4, 93: 2, 94: 2, 95: 1}   # b4a1x runs of the previous job (no solutions)
nr = {}
orders = sorted(set(a1) | set(a2) | set(prev))
out = subprocess.run(['gap', '-q'], input='for n in [' + ','.join(map(str, orders)) + '] do Print(n, " ", NrSmallGroups(n), "\\n"); od; QUIT;',
                     capture_output=True, text=True).stdout
for ln in out.split('\n'):
    t = ln.split()
    if len(t) == 2: nr[int(t[0])] = int(t[1])
print('| order | vertices | groups | [[1,4],[4,1]] (b4a1x): groups done, groups with solutions | [[2,3],[3,2]] (b4a2y): groups done, groups with solutions |')
print('|---:|---:|---:|---|---|')
for o in orders:
    def cell(d, o):
        if o not in d: return 'not run'
        done = len(d[o]); hits = sorted(i for i, s in d[o].items() if s)
        return f"{done}/{nr.get(o, '?')}" + (f", solutions in {hits}" if hits else ", none")
    c1 = cell(a1, o) if o in a1 else (f"{prev[o]}/{prev[o]}, none (previous job)" if o in prev else 'not run')
    print(f"| {o} | {4 * o} | {nr.get(o, '?')} | {c1} | {cell(a2, o)} |")
