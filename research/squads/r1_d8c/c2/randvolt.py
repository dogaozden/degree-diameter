"""Control: same base graph as flagrule.py (flags vs copies, 4 star + 2 matching edges per flag), but every base edge
gets an independent uniform voltage in Z5 (random Z5-lift of the 2912-vertex base). Exact check: gcheck range:0:2912."""
import sys, random, subprocess, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import flagrule as fr
GC = '/home/user/degree-diameter/research/squads/cells/d10D8_work/gcheck'
B, F, N, NL = fr.B, fr.F, fr.N, fr.NL
res = []
for seed in range(int(sys.argv[1])):
    rng = random.Random(seed)
    col = fr.colouring(seed % 5)
    sig = [rng.sample(range(4), 4), rng.sample(range(4), 4)]
    E = set()
    for i in range(NL):
        for f in range(F):
            p, l = fr.flag_p[f], fr.flag_l[f]
            base_edges = []
            for tt in range(4):
                e = p if tt < 2 else l
                base_edges.append((F + tt * N + e, rng.randrange(NL)))
            for j in range(2):
                T = sig[j][col[f]]
                e = p if T < 2 else l
                base_edges.append((F + T * N + e, rng.randrange(NL)))
            for c, v in base_edges:
                u = i * B + f; w = ((i + v) % NL) * B + c
                E.add((min(u, w), max(u, w)))
    fn = f'graphs/rv{seed}.txt'
    with open(fn, 'w') as fh:
        fh.write(f'{NL*B}\n' + '\n'.join(f'{a} {b}' for a, b in sorted(E)) + '\n')
    r = subprocess.run([GC, fn, '8', 'range:0:2912'], capture_output=True, text=True)
    os.remove(fn)
    res.append((int(r.stdout.split()[1]), len(E), r.stdout.split()[9] if len(r.stdout.split())>9 else ''))
    print(seed, res[-1], flush=True)
print('min', min(res))
