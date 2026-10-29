import sys, os
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
from hexload import load
from transcheck import bad_pairs
DATA = '/home/user/degree-diameter/research/squads/conics2-r1/data/hex_q5.bin'
q, N, LP, PL, X = load(DATA)

def score(sig, R):
    return bad_pairs(q, N, LP, PL, np.asarray(sig, np.int64), np.asarray(sorted(R), np.int64))

def load_rec():
    sig = np.array([int(t) for t in open('/home/user/degree-diameter/research/squads/conics2-r1/c3/sigma_rec.txt').read().split()], np.int64)
    R = [int(t) for t in open('/home/user/degree-diameter/research/squads/conics2-r1/c3/R_rec.txt').read().split()]
    return sig, R

def save(sig, R, fn):
    with open(fn, 'w') as f:
        f.write('multi 5 3906 1 %d %d %d 0\n' % (len(R), len(R), len(R)))
        f.write('freed ' + ' '.join(map(str, sorted(R))) + '\n')
        f.write('hubedges -\n')
        for i in range(0, N, 20):
            f.write(' '.join(map(str, sig[i:i+20])) + '\n')
