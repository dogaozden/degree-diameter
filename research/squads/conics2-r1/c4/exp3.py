import sys, subprocess
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics2-r1/c4')
from exp2 import *
hubK = add_hub_pair(hub0, K0, random.Random(1))
for x0 in [int(t) for t in sys.argv[1:]]:
    n, E = build(q, N, LP, sig, R0 + [x0], hubK, K0 + 1, K0 + 1)
    write_edges('/home/user/degree-diameter/research/squads/conics2-r1/c4/tmp_h.edges', n, E)
    print('x0', x0, 'sigma(x0)', int(sig[x0]))
    print(subprocess.run(['./count7h', 'tmp_h.edges', '7', str(N)], capture_output=True, text=True).stdout)
