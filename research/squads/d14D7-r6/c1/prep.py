# export inputs for cann.c: R (756 point ids), S (1332 line ids), initial state (k, X, L) as text
import numpy as np, sys
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
OUT = SP + 'r6_c1/'
R = np.load(SP + 'R756idx.npy').astype(np.int64)
S = np.load(SP + 'S_herm.npy').astype(np.int64)
np.savetxt(OUT + 'R756.txt', R, fmt='%d')
np.savetxt(OUT + 'S.txt', S, fmt='%d')
st = np.load(sys.argv[1])
with open(OUT + 'init.txt', 'w') as f:
    f.write(f"{len(st['X'])}\n" + ' '.join(map(str, st['X'])) + '\n' + ' '.join(map(str, st['L'])) + '\n')
print('R', len(R), 'S', len(S), 'k', len(st['X']))
