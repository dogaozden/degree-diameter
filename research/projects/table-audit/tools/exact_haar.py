"""Try to reach a table value exactly with a Haar graph (table-audit): for a cell (d, D, N) try group specs of order N/2
with research/frontier/haar_gen3 (annealing) until one gives diameter <= D.  Specs: every metacyclic Z_m x|_r Z_k
(one r per subgroup <r>, larger ord(r) first), the cyclic group, and psl/pgl/sl/agl1 when the order matches.
Usage: exact_haar.py HAAR_GEN3 OUTDIR SECONDS_PER_SPEC d D N [d D N ...]   -> OUTDIR/results.jsonl, OUTDIR/*.sol"""
import json, math, os, subprocess, sys

def metas(N):
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        seen = set()
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1:
                continue
            sub = frozenset(pow(r, j, m) for j in range(k))
            if sub in seen:
                continue
            seen.add(sub)
            o = next(j for j in range(1, k + 1) if pow(r, j, m) == 1)
            out.append((o, m, k, r))
    out.sort(key=lambda x: (-x[0], x[1]))
    return [f'meta {m} {k} {r}' for o, m, k, r in out]

def prime_powers(lim):
    pp = []
    for q in range(2, lim):
        p = next(t for t in range(2, q + 1) if q % t == 0)
        x = q
        while x % p == 0:
            x //= p
        if x == 1:
            pp.append(q)
    return pp

def specs(N):
    s = []
    for q in prime_powers(200):
        for name, order in (('psl', q * (q * q - 1) // math.gcd(2, q - 1)), ('sl', q * (q * q - 1)),
                            ('pgl', q * (q * q - 1)), ('agl1', q * (q - 1))):
            if order <= N and N % order == 0 and (name != 'pgl' or q % 2):
                s.append((f'{name} {q}', N // order))
    return [(m, 1) for m in metas(N)] + s + [('cyc', N)]

haar, outdir, secs = sys.argv[1], sys.argv[2], int(sys.argv[3])
MAXSPECS = int(os.environ.get('MAXSPECS', '100000'))   # try at most this many group specs per cell
SEEDS = int(os.environ.get('SEEDS', '1'))             # seeds per spec
os.makedirs(outdir, exist_ok=True)
args = list(map(int, sys.argv[4:]))
for i in range(0, len(args), 3):
    d, D, NN = args[i:i + 3]
    N = NN // 2
    found = False
    for spec, n in [sn for sn in specs(N)][:MAXSPECS]:
      for seed in range(1, SEEDS + 1):
        sol = f'{outdir}/d{d}D{D}_n{NN}_{spec.replace(" ", "_")}_x{n}.sol'
        cmd = [haar, str(d), str(D), str(secs), str(seed), '8', sol] + spec.split() + [str(n)]
        try:
            r = subprocess.run(['nice', '-n', '10'] + cmd, capture_output=True, text=True, timeout=secs + 60)
            txt = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            txt = 'timeout'
        ok = 'full diameter check: OK' in txt and os.path.exists(sol)
        best = [l for l in txt.splitlines() if l.startswith('RESULT')]
        rec = dict(d=d, D=D, n=NN, spec=spec, zn=n, seed=seed, ok=ok, result=best[-1] if best else txt[-200:], sol=sol if ok else None)
        with open(f'{outdir}/results.jsonl', 'a') as f:
            f.write(json.dumps(rec) + '\n')
        print(json.dumps(rec), flush=True)
        if ok:
            found = True
            break
      if found:
        break
