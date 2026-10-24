# Runs named.py on metacyclic groups Z_M x|_R Z_k given as permutation groups (affine maps x -> x+1, x -> R*x mod M).
import subprocess, sys, os
OUT = '/home/user/degree-diameter/research/squads/r1-smallfam/c6'
NAMED = '/home/user/degree-diameter/research/theorems/smallfam'

def expr(M, R):
    return (f"Group(PermList(List([0..{M-1}], x -> ((x+1) mod {M}) + 1)), "
            f"PermList(List([0..{M-1}], x -> (({R}*x) mod {M}) + 1)))")

D = int(sys.argv[1])
pairs = [tuple(map(int, p.split(':'))) for p in sys.argv[2:]]   # M:R
exprs = [expr(M, R) for M, R in pairs]
cmd = ['timeout', '900', 'nice', '-n', '10', 'python3', os.path.join(NAMED, 'named.py'), '4', str(D), *exprs,
       '--threads', '1', '--outdir', OUT]
env = dict(os.environ, THREADS='1')
subprocess.run(cmd, cwd=NAMED, env=env)
