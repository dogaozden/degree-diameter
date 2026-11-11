#!/usr/bin/env python3
"""Job list for poolbuild.py from generated folders: parts, then data/levels, then checks, then records.
usage: joblist.py MODPREFIX DIR [DIR ...]   (prints MOD:GB tokens with '--' barriers)"""
import os, sys
pref = sys.argv[1]
dirs = sys.argv[2:]
stages = [[], [], [], []]
for d in dirs:
    g = os.path.basename(d.rstrip('/'))
    for f in sorted(os.listdir(d)):
        if not f.endswith('.lean'):
            continue
        m = f'{pref}.{g}.{f[:-5]}'
        if f.startswith('P_'):
            stages[0].append(f'{m}:3')
        elif f == 'Data.lean' or f.startswith('Lev'):
            stages[1].append(f'{m}:2.5')
        elif f == 'Record.lean':
            stages[3].append(f'{m}:2')
        elif f.startswith('Step') or f.startswith('Bfs'):
            stages[2].append(f'{m}:4.5')
        else:
            stages[2].append(f'{m}:5')
out = []
for s in stages:
    out += s + ['--']
print(' '.join(out[:-1]))
