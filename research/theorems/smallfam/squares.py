"""The 'squares' Frobenius groups G_p = Z_p x| Z_(p-1)/2 (r = g^2, g a primitive root), exhaustive in normal form,
for one (Delta, D) and a list of primes.  Usage: python3 squares.py DELTA D p1 p2 ... [--threads T]"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
SP = os.environ.get('SCRATCH', '/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad')
args = [a for a in sys.argv[1:] if not a.startswith('--')]
threads = int(sys.argv[sys.argv.index('--threads') + 1]) if '--threads' in sys.argv else 3
if '--threads' in sys.argv:
    args.remove(str(threads))
Delta, D, ps = int(args[0]), int(args[1]), [int(x) for x in args[2:]]
for p in ps:
    g = next(c for c in range(2, p) if all(pow(c, (p - 1) // q, p) != 1 for q in {q for q in range(2, p) if (p - 1) % q == 0 and all(q % t for t in range(2, int(q ** .5) + 1))}))
    r, k = g * g % p, (p - 1) // 2
    plan = os.path.join(SP, f'sq_plan_{p}.txt')
    with open(plan, 'w') as f:
        for j1 in range(1, k):
            for j2 in range(k):
                f.write(f'{j1} {k + j2}\n')
    out = subprocess.run([os.path.join(HERE, 'hx'), 'meta', str(p), str(k), str(r), str(Delta), str(D), plan, '20'],
                         capture_output=True, text=True, env=dict(os.environ, THREADS=str(threads), QFILTER='1')).stdout
    sols = [l for l in out.splitlines() if l.startswith('SOL')]
    dl = [l for l in out.splitlines() if l.startswith('DONE')][0]
    N = p * k
    print(f'p={p} (mod 4 = {p % 4}) k={k} r={r} N={N} n={2*N} {dl}', flush=True)
    if sols:
        with open(os.path.join(HERE, 'runs', f'squares_d{Delta}D{D}_p{p}.txt'), 'w') as f:
            f.write(f'# Haar graph Delta={Delta} D={D} G = Z_{p} x|_{r} Z_{k} (squares group), N={N} n={2*N}; elements a*k+j\n')
            f.write('\n'.join(sols) + '\n')
    os.remove(plan)
