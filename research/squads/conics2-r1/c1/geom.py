import os, sys
os.environ.setdefault('OMP_NUM_THREADS', '1'); os.environ.setdefault('OPENBLAS_NUM_THREADS', '1')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
from hexload import load

DATA = '/home/user/degree-diameter/research/squads/conics2-r1/data'

def build(q=5):
    q_, N, LP, PL, X = load(f'{DATA}/hex_q{q}.bin')
    L = LP.shape[0]
    Inc = np.zeros((N, L), np.float32)           # point x line
    Inc[np.repeat(np.arange(L), q + 1), LP.reshape(-1)] = 1
    Inc = Inc.T.copy()                            # keep as (L x N) for later
    Inc = Inc.T                                   # N x L
    pc = (Inc @ Inc.T) > 0                        # collinear incl diag
    np.fill_diagonal(pc, False)
    A = pc.astype(np.float32)
    A2 = (A @ A) > 0
    I = np.eye(N, dtype=bool)
    d4 = A2 & ~pc & ~I                            # points at distance 4 (incidence)
    opp = ~(pc | d4 | I)
    lc = (Inc.T @ Inc) > 0                        # lines concurrent incl diag
    np.fill_diagonal(lc, False)
    Bl = lc.astype(np.float32)
    Bl2 = (Bl @ Bl) > 0
    IL = np.eye(L, dtype=bool)
    d4l = Bl2 & ~lc & ~IL
    oppl = ~(lc | d4l | IL)
    return dict(q=q, N=N, L=L, LP=LP, PL=PL, X=X, pc=pc, d4=d4, opp=opp, lc=lc, d4l=d4l, oppl=oppl, Inc=Inc)

def read_spread(fn, L_count=None):
    ids = [int(t) for line in open(fn) if not line.startswith('#') for t in line.split()]
    return ids
