import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r4/h01')
import scan
nm = sys.argv[1]; volt = [int(x) for x in sys.argv[2].split(',')]; out = sys.argv[3]
T = scan.load_bin(f'/home/user/degree-diameter/research/squads/b48/r4/h01/groups/{nm}.bin'); N = len(T)
base = [(0,2),(0,2),(0,3),(1,2),(1,3),(1,3)]
E = []
for (u, v), g in zip(base, volt):
    for x in range(N):
        E.append((u*N + x, v*N + int(T[g, x])))
with open(out, 'w') as f:
    f.write(f'{4*N}\n')
    f.write('\n'.join(f'{a} {b}' for a, b in E) + '\n')
print('wrote', out, 'n', 4*N, 'edges', len(E))
