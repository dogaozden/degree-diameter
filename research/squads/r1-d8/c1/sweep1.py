"""Sweep: q=5, k in KS, rules x labspecs, seeds; prints unreached at D=8 (all sources)."""
import sys
import pencil
import gh

q = 5
H = gh.load(q)
KS = [int(x) for x in sys.argv[1].split(',')]
RULES = sys.argv[2].split(',')
LABS = sys.argv[3].split(',')
SEEDS = [int(x) for x in sys.argv[4].split(',')]
M2S = [int(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else [1]
FLAGV = sys.argv[6] if len(sys.argv) > 6 else 'zero'
for k in KS:
    for rule in RULES:
        for lab in LABS:
            for m2 in M2S:
                res = []
                for s in SEEDS:
                    unr, ecc = pencil.run(H, q, k, rule, lab, s, m2, FLAGV)
                    res.append((unr, ecc))
                print(f'M={5*k} k={k} rule={rule} labels={lab} m2={m2} flagv={FLAGV} res(unreached,max_ecc)={res}', flush=True)
