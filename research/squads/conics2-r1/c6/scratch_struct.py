import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/tools')
import numpy as np
from hexload import load
D = '/home/user/degree-diameter/research/squads/conics2-r1/data/'
for q in [4, 5, 7]:
    qq, N, LP, PL, X = load(D + f'hex_q{q}.bin')
    txt = open(D + f'spread_lines_q{q}.txt').read().split('\n')
    nums = [t for t in txt if t.strip() and not t.startswith('#')]
    for k, ln in enumerate(nums):
        S = sorted(set(int(t) for t in ln.split()))
        # pairwise intersections of lines in S
        cnt = np.zeros(N, int)
        for l in S:
            cnt[LP[l]] += 1
        shared = int((cnt >= 2).sum())
        pts = int((cnt >= 1).sum())
        # per-line count of shared points
        print(f'q={q} row{k}: #lines={len(S)} distinct points covered={pts} (={len(S)*(q+1)} if disjoint) shared points={shared}')
    # RH and RL sets
    for name in ['RH_spread', 'RL_whisk']:
        s = sorted(set(int(t) for t in open(D + f'{name}_q{q}.txt').read().split()))
        print(q, name, len(s), 'max idx', max(s) if s else None, 'N', N)
