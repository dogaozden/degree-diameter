import sys, os
import numpy as np
D = '/home/user/degree-diameter/research/squads/conics2-r1'
sys.path.insert(0, D + '/tools')
from hexload import load

def read_ints(fn):
    return [int(t) for t in open(fn).read().split() if t.lstrip('-').isdigit()]

def setup(q):
    q_, N, LP, PL, X = load(f'{D}/data/hex_q{q}.bin')
    G = np.unique(np.array(read_ints(f'{D}/data/RL_whisk_q{q}.txt'), dtype=np.int64))
    spread_pts = np.unique(np.array(read_ints(f'{D}/data/RH_spread_q{q}.txt'), dtype=np.int64))
    sl_lines = [l for l in open(f'{D}/data/spread_lines_q{q}.txt').read().split('\n') if l and not l.startswith('#')]
    spread_lines = np.array([int(t) for t in sl_lines[0].split()], dtype=np.int64)
    v = int([l for l in open(f'{D}/data/spread_lines_q{q}.txt').read().split('\n') if l.startswith('# v')][0].split('=')[1])
    return q, N, LP, PL, X, G, spread_pts, spread_lines, v

def valid(LP, PL, N, G):
    inG = np.zeros(N, bool); inG[G] = True
    cnt = inG[PL].sum(1)
    bad = int(((cnt[LP[G]] >= 2).sum(1) > 1).sum())
    return bad == 0
