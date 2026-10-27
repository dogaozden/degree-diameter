import sys, glob, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools'); from q6lib import Geo
G = Geo(13)
base = set(int(x) for x in open('/home/user/degree-diameter/research/d10D7/sets/P13_E7sub_E6_792.txt').read().split())
for f in sorted(glob.glob('/home/user/degree-diameter/research/squads/hexfam_r2/c4/A_*_792.txt')):
    R = np.array([int(x) for x in open(f).read().split()])
    B = G.B(G.C[R], G.C[R]) == 0
    np.fill_diagonal(B, False)
    print(f.split('/')[-1], len(R), len(set(R.tolist())), 'close pairs', int(B.sum()//2), 'overlap with P13', len(base & set(R.tolist())))
