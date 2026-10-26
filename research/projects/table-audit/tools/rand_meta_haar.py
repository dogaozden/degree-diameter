"""Random Haar graphs of a metacyclic group, for cells where haar_gen3 cannot run (groups with no element of order
2..63, e.g. Z_p x| Z_k with p, k prime > 63; haar_gen3 then has no coset bitsets and crashes) (table-audit-2).
S = {e} + d-1 random distinct elements; each candidate is written as a haar_gen3-style solution file and checked
exactly by meta_haar_bits (two-side bitset BFS).  Stops at the first graph with diameter <= D.
usage: rand_meta_haar.py MHB_BINARY OUTDIR d D m k r TRIES SEED"""
import os, random, subprocess, sys
mhb, out, d, D, m, k, r, tries, seed = sys.argv[1], sys.argv[2], *map(int, sys.argv[3:10])
assert pow(r, k, m) == 1
os.makedirs(out, exist_ok=True)
rng = random.Random(seed)
n = 2 * m * k
for t in range(tries):
    S = {(0, 0)}
    while len(S) < d:
        S.add((rng.randrange(m), rng.randrange(k)))
    S = sorted(S)
    sol = os.path.join(out, f'd{d}D{D}_n{n}_meta_{m}_{k}_{r}_x1.sol')
    with open(sol + '.try', 'w') as f:
        f.write(f'{d} {D} meta {m} {k} {r} n 1 N {m * k}\n')
        for a, j in S:
            f.write(f'{a * k + j} meta(a={a},j={j}) z=0\n')
    res = subprocess.run([mhb, sol + '.try'], capture_output=True, text=True).stdout
    last = res.strip().splitlines()[-1] if res.strip() else 'no output'
    print(f'try {t}: {" ".join(l for l in res.splitlines() if l.startswith("ecc"))} {last}', flush=True)
    if last.startswith('RESULT VALID'):
        os.replace(sol + '.try', sol); print('found', sol); break
