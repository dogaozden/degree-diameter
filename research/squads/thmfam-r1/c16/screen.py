#!/usr/bin/env python3
"""Screen c16 candidates: runs family_score.py on --qs (default 29,41,53) and prints mean_excess per candidate."""
import subprocess, json, sys, itertools, random
SC = '/home/user/degree-diameter/research/theorems/haar_families'
GEN = '/home/user/degree-diameter/research/squads/thmfam-r1/c16/gen_c16.py'
QS = '29,41,53'
def score(args, group='psl', qs=QS):
    cmd = ['python3', GEN] + args
    gen = ' '.join(cmd)
    r = subprocess.run(['nice', '-n', '10', 'timeout', '900', 'python3', SC + '/family_score.py',
                        '--gen', gen, '--group', group, '--qs', qs, '--json'],
                       capture_output=True, text=True, cwd=SC)
    try:
        out = json.loads(r.stdout)
    except Exception:
        return None, r.stdout[-300:] + r.stderr[-300:]
    s = out['summary']
    return s['mean_excess'], out['rows']
