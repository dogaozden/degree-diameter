import sys, json, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r1/c09')
from orbit import meta_table
m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
S = [int(v) for v in sys.argv[4].split(',')]
T = meta_table(m, k, r); N = m * k
edges = []
for g in S:
    for x in range(N):
        edges.append((x, N + int(T[x, g])))
fn = '/home/user/degree-diameter/research/squads/b48/r1/c09/check_tmp.edges'
with open(fn, 'w') as f:
    f.write("%d\n" % (2 * N))
    f.write("\n".join("%d %d" % e for e in edges) + "\n")
print(subprocess.run(['/home/user/degree-diameter/research/squads/b48/tools/score48', fn], capture_output=True, text=True).stdout[-600:])
