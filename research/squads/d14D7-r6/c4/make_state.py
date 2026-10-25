import pickle, sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
best_F, info = pickle.load(open(sys.argv[1], 'rb'))
T = info['row']; assign = info['assign']
X = [int(T[t]) for t in sorted(assign)]; L = [int(assign[t]) for t in sorted(assign)]
R = np.load(SP + 'R756idx.npy')
np.savez(sys.argv[2], X=np.array(X, dtype=np.int64), L=np.array(L, dtype=np.int64), R=R)
print('F', best_F, 'k', len(X), 'T-index', sorted(assign), 'M', info['M'], 'm', info['m'], 'T', T)
