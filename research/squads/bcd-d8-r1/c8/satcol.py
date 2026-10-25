import sys, time, threading, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/bcd-d8-r1/c8/pylib')
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs
from pysat.solvers import Solver
K = 7
H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin')
N = H.N
var = lambda p, c: p * K + c + 1
clauses = []
for p in range(N):
    clauses.append([var(p, c) for c in range(K)])
for L in range(N):
    pts = [int(x) for x in H.lines[L]]
    for i in range(len(pts)):
        for j in range(i + 1, len(pts)):
            for c in range(K):
                clauses.append([-var(pts[i], c), -var(pts[j], c)])
# symmetry breaking: first line gets colours 0..5
for i, p in enumerate([int(x) for x in H.lines[0]]):
    clauses.append([var(p, i)])
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
tlim = float(sys.argv[2]) if len(sys.argv) > 2 else 240
random.seed(seed)
random.shuffle(clauses)
s = Solver(name='cadical153', bootstrap_with=clauses)
timer = threading.Timer(tlim, lambda: s.interrupt())
timer.start()
t0 = time.time()
res = s.solve_limited(expect_interrupt=True)
timer.cancel()
print("result", res, "time", round(time.time() - t0, 1), flush=True)
if res:
    model = set(l for l in s.get_model() if l > 0)
    col = []
    for p in range(N):
        cs = [c for c in range(K) if var(p, c) in model]
        col.append(cs[0])
    sizes = [col.count(c) for c in range(K)]
    print("sizes", sizes, flush=True)
    with open(f'col7_sat_{seed}.txt', 'w') as f:
        f.write("\n".join(map(str, col)) + "\n")
    print("saved")
