"""Structure of a relaxed set of W(q): size, pairs, pairs on regular-spread lines, points per spread line, and the
counting slack.  usage: python3 analyze.py q setfile   (setfile: rtabu output or a json list)"""
import sys, os, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
q = int(sys.argv[1]); s = open(sys.argv[2]).read()
T = json.loads(s) if s.strip().startswith('[') else [int(x) for x in s.split()[1:]]
if isinstance(T, dict): T = T['T']
pre = os.path.join(HERE, 'data', 'W%d' % q)
adj = [list(map(int, l.split()[1:])) for l in open(pre + '_adj.txt').read().strip().split('\n')[1:]]
sp = list(map(int, open(pre + '_spread.txt').read().split()))
Ts = set(T); deg = {v: sum(1 for u in adj[v] if u in Ts) for v in T}
assert len(Ts) == len(T) and max(deg.values()) <= 1, 'not relaxed'
pairs = [(v, u) for v in T for u in adj[v] if u in Ts and v < u]
onS = sum(1 for v, u in pairs if sp[v] == sp[u])
per = np.bincount([sp[v] for v in T], minlength=q * q + 1)
n = (q + 1) * (q * q + 1); bound = 2 * (q + 1) * (q * q + 1) // (2 * q + 1)
print('q=%d |T|=%d singles=%d pairs=%d (on spread lines %d); spread lines with 0/1/2 points: %s; counting bound %d; '
      'lines met %d of %d' % (q, len(T), len(T) - 2 * len(pairs), len(pairs), onS, np.bincount(per).tolist(), bound,
                              (q + 1) * len(T) - len(pairs), n))
