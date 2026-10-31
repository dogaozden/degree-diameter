# randvolt.py IN OUT SEED M: re-draw all voltages uniformly in Z_M (keeps the structure)
import sys, random
rnd = random.Random(int(sys.argv[3])); M = int(sys.argv[4])
L = open(sys.argv[1]).read().split('\n')
out = L[:2]
for line in L[2:]:
    p = line.split()
    if len(p) >= 2:
        out.append(f"{p[0]} {p[1]} {rnd.randrange(M)}")
open(sys.argv[2], 'w').write('\n'.join(out) + '\n')
