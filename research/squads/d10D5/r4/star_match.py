#!/usr/bin/env python3
"""star_match.py "p:l p:l ...": is there a sigma with exact coverage for every freed flag (flagmatch.py) AND the
star condition of the FLAGDEL variant (sigma maps the non-freed points of l_i other than p_i onto non-freed lines
through p_i other than l_i, and back)?  Together: sigma(p_i^perp) = l_i^perp class by class.  Prints the maximum
matching size; with OUT=file writes a sigma (perfect matchings only) as one line."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'hubs'))
from gq import load
import flagmatch
q, N, lines, lof = load(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'gq', 'gq_q7.bin'))
flags = [tuple(map(int, t.split(':'))) for t in sys.argv[1].split()]
mode = os.environ.get('MODE', 'both')   # both | exact | star
F = {p for p, l in flags}; Fl = {l for p, l in flags}
if mode == 'star':
    adj = [[dict(flags)[x]] if x in F else [M for M in range(N) if M not in Fl] for x in range(N)]
else:
    adj = flagmatch.setup(q, N, lines, lof, flags)
if mode != 'exact':
    B = [set(lines[l]) - {p} - F for p, l in flags]
    Sx = [set(lof[p]) - {l} - Fl for p, l in flags]
    for x in range(N):
        if x in F: continue
        row = adj[x]
        for i in range(len(flags)):
            if x in B[i]: row = [M for M in row if M in Sx[i]]
        row = [M for M in row if all(x in B[i] for i in range(len(flags)) if M in Sx[i])]
        adj[x] = row
size, mL = flagmatch.hk(adj, N, N)
print('k', len(flags), 'mode', mode, 'matching', size, 'of', N, '| star sizes', [(len(set(lines[l]) - {p} - F), len(set(lof[p]) - {l} - Fl)) for p, l in flags] if mode != 'exact' else '')
if os.environ.get('OUT') and size == N:
    open(os.environ['OUT'], 'w').write(' '.join(map(str, mL)) + '\n')
