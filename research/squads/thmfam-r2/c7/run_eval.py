#!/usr/bin/env python3
"""One haar_ecc evaluation of an LPS(p) x Z_m cover. Usage: run_eval.py p q m MODE [ARGS]
MODE arith            : labels z = a1 + a2 r + a3 r^2 mod m (gen_lps_cover.py arith)
MODE cyc SEED         : 3-cycles get (t, rt, r^2 t) with t drawn at random from SEED (t1 = 1 fixed to a unit)
Appends one JSON line to evals.jsonl (in this folder)."""
import sys, subprocess, random, json, os, time
HERE = '/home/user/degree-diameter/research/squads/thmfam-r2/c7'
TH = '/home/user/degree-diameter/research/theorems/haar_families'
p, q, m, mode = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
if mode == 'arith':
    gen = ['python3', f'{TH}/gen_lps_cover.py', str(p), str(q), str(m), 'arith']
else:
    seed = int(sys.argv[5])
    show = subprocess.run(['python3', f'{TH}/gen_lps_cover.py', str(p), str(q), str(m), 'zero', '--show'],
                          capture_output=True, text=True)
    n3 = show.stderr.count("), (") if False else None
    # count 3-cycles: the --show line lists cycles as "[(..), (..), (..)]"; each 3-cycle contributes one list
    cyc_txt = show.stderr.split('cycles', 1)[1]
    n3 = cyc_txt.count('[(') if '[(' in cyc_txt else 0
    rng = random.Random(seed)
    ts = [1] + [rng.randrange(1, m) if m > 1 else 0 for _ in range(n3 - 1)] if n3 else []
    gen = ['python3', f'{TH}/gen_lps_cover.py', str(p), str(q), str(m), 'cyc'] + [str(t) for t in ts]
t0 = time.time()
g = subprocess.run(gen, capture_output=True, text=True)
if g.returncode:
    print('GEN FAILED', g.stderr[-300:]); sys.exit(1)
h = subprocess.run(['nice', '-n', '10', 'timeout', '900', f'{TH}/haar_ecc', 'pgl', str(q), str(m)],
                   input=g.stdout, capture_output=True, text=True)
line = [l for l in h.stdout.splitlines() if l.startswith('RESULT')]
rec = {'p': p, 'q': q, 'm': m, 'mode': mode, 'args': sys.argv[5:], 'Delta': p + 1, 'raw': line[-1] if line else h.stdout[-300:] + h.stderr[-300:]}
if line:
    import re
    d = dict(re.findall(r'(\w+)=(\S+)', line[-1]))
    V = q * (q * q - 1) * m
    rec.update({'ecc_A': int(d['ecc_A']), 'ecc_B': int(d['ecc_B']), 'compA': int(d['compA']), 'V': V,
                'full': int(d['compA']) == V and int(d['compB']) == V, 'diam': max(int(d['ecc_A']), int(d['ecc_B']))})
rec['sec'] = round(time.time() - t0, 1)
with open(os.path.join(HERE, 'evals.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
print(json.dumps(rec))
