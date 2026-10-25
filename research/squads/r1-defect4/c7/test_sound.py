"""Soundness check for gen.py symmetry breaking: for small square (n,k) instances, the plain and the
double-lex CNFs must agree on SAT/UNSAT. Uses kissat (scratchpad binary) on each CNF."""
import subprocess, sys, os, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen
K = '/tmp/claude-0/-home-user-degree-diameter/4905f117-080d-5578-b5d8-53a7377d03a3/scratchpad/kissat/build/kissat'
tmp = tempfile.mkdtemp(dir=os.path.dirname(os.path.abspath(__file__)))
def status(cnf, name):
    path = os.path.join(tmp, name + '.cnf'); cnf.to_file(path)
    r = subprocess.run(['timeout', '120', K, '-q', path], capture_output=True, text=True)
    return {10: 'SAT', 20: 'UNSAT'}.get(r.returncode, 'TO')
cases = [(3, 7), (3, 9), (4, 13), (4, 11), (4, 9), (4, 12), (3, 6), (5, 16), (5, 17), (4, 10), (3, 8)]
for k, n in cases:
    a = status(gen.build(k, symbreak=False, n=n), f'p{k}_{n}')
    b = status(gen.build(k, symbreak=True, n=n), f's{k}_{n}')
    print(f'k={k} n={n} plain={a} doublelex={b} {"OK" if a == b else "MISMATCH"}', flush=True)
