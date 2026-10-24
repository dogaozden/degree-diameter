"""dmstart.py q out seed [mode] : lift2 solution file for the doubled-matching construction DM:
J=2 matchings with sigma_2 = sigma_1 (a random matching, each matching edge doubled), group Z_6, matching voltages
1 and 4, hexagon voltages in {0,3}: mode 'rand' (random 0/3), 'zero' (all 0)."""
import random, struct, sys
q, out, seed = int(sys.argv[1]), sys.argv[2], int(sys.argv[3])
mode = sys.argv[4] if len(sys.argv) > 4 else 'rand'
random.seed(seed)
with open(f'hex/hex_q{q}.bin', 'rb') as f:
    qq, N, L = struct.unpack('3i', f.read(12))
sig = list(range(N)); random.shuffle(sig)
with open(out, 'w') as f:
    f.write(f"{q} 2 6 7 -1\ncyc 6\n")
    f.write(' '.join(map(str, sig)) + '\n'); f.write(' '.join(map(str, sig)) + '\n')
    f.write(' '.join(['1'] * N) + '\n'); f.write(' '.join(['4'] * N) + '\n')
    f.write(' '.join(str(3 * random.randrange(2)) if mode == 'rand' else '0' for _ in range(N * (q + 1))) + '\n')
