"""write_score.py M VALID: append the c4 scoreboard line for the best Singer-invariant design with m = M."""
import json, sys
M = int(sys.argv[1]); valid = sys.argv[2].lower() == 'true'
C4 = '/home/user/degree-diameter/research/squads/r1_d14D8/c4'
q = 11
N = 177156
line = {
    "card": "c4",
    "idea": "Singer-torus-invariant voltage lifts of H(11) (Sigma = <C^10>, |Sigma| = 133): hexagon and matching "
            "voltages constant on Sigma-orbits; annealing over 18648 quotient-edge voltages, COST on sampled orbit reps, "
            "full check on all 1332 orbit reps",
    "code": f"{C4}/symsa.c",
    "command": f"cd {C4} && python3 sym_setup.py 1 && python3 mkbase.py run1_m{M}.txt base_m{M}.txt 1 {M} && "
               f"REPS=$(python3 -c \"import numpy as np; print(','.join(str(int(x)) for x in np.load('sym_1.npz')['repP']))\") && "
               f"/home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval base_m{M}.txt 8 i:$REPS",
    "q": q,
    "score": M if valid else 0,
    "vertices": M * 2 * N,
    "dgq_m": 5 * (q + 5) // 2,
    "valid": valid,
    "next": "longer annealing with a faster DP (cost on bad reps only, incremental per-edge update), starting from the best m",
}
with open(f'/home/user/degree-diameter/research/squads/r1_d14D8/scoreboard.jsonl', 'a') as f:
    f.write(json.dumps(line) + '\n')
print(json.dumps(line))
