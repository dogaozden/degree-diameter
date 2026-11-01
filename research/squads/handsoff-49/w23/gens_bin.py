import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w15')
from bfs15 import load_bin
T = load_bin(sys.argv[1]); N = len(T)
random.seed(1)
for _ in range(2000):
    g = random.sample(range(1, N), 2)
    S = {0}; fr = [0]
    while fr:
        nw = []
        for h in fr:
            for s in g:
                x = int(T[h, s])
                if x not in S:
                    S.add(x); nw.append(x)
        fr = nw
    if len(S) == N:
        print(','.join(map(str, g))); break
