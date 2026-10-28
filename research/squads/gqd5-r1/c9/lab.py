"""c9 test bed: 3 levels, types D,H,H over G=Q4(q). Transitions t0=(0,1): D->H friendly, M0 = identity on lines;
t1=(1,1): H->H non-friendly, M1 = points(lvl1) -> lines(lvl2) fixed bijection; t2=(2,1): H->D friendly, identity on points."""
import sys, os, subprocess, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import Q4
from levels import build, write_edges

HERE = os.path.dirname(os.path.abspath(__file__))
Q = 5
G = Q4(Q)
NP, NL = G.np, G.nl
TYPES = ['D', 'H', 'H']
D_DEG = Q + 1 + 1   # degree bound q+2
M = {(0, 1): np.arange(NL), (1, 1): np.arange(NP), (2, 1): np.arange(NP)}
# M1 uses identity index map point p -> line p (any bijection works, Theorem A)

def graph(R0=(), R1=(), R2=(), Bh=(), Ah=(), Y=()):
    """Bh: list of (line_l, point_p1, point_p2) B-hub slots at levels 0,1,2. Ah: list of (lvl0 point, lvl1 line, lvl2 line)
    A-hub slots; these are converted to the levels.build format."""
    R = {(0, 1): set(R0), (1, 1): set(R1), (2, 1): set(R2)}
    # B-hub slots
    bh = []
    for (l, p1, p2) in Bh:
        bh.append([(0, l, (0, 1)), (1, p1, (1, 1)), (2, p2, (2, 1))])
    ah = []
    for (b0, b1, b2) in Ah:
        # level 0 B-element point b0 = M2(a) with a in R2 (identity): t=(2,1); level 1 line b1 = M0(a), a in R0: t=(0,1);
        # level 2 line b2 = M1(a), a in R1: t=(1,1)
        ah.append([(0, b0, (2, 1)), (1, b1, (0, 1)), (2, b2, (1, 1))])
    n, E = build(G, TYPES, M, R, bh, ah, list(Y))
    return n, E

def bad(n, E, D=5, tag='tmp'):
    p = os.path.join(HERE, 'tmp_%s.txt' % tag)
    write_edges(p, n, E)
    out = subprocess.run([os.path.join(HERE, 'badcount'), p, str(D)], capture_output=True, text=True).stdout.strip()
    parts = out.split()
    return dict(maxdeg=int(parts[1]), maxdist=int(parts[3]), bad=int(parts[5]), n=int(parts[7]))

def apsp_valid(n, E, tag='tmp'):
    p = os.path.join(HERE, 'tmp_%s.txt' % tag)
    write_edges(p, n, E)
    out = subprocess.run(['/home/user/degree-diameter/research/theorems/d5gq/apsp', p, str(D_DEG), '5'],
                         capture_output=True, text=True).stdout.strip()
    return out
