import sys
import controller as ct
T = ct.parse(sys.argv[1])
with open(sys.argv[2], 'w') as f:
    f.write(f"{len(T)}\n"); f.write(' '.join(map(str, T.flatten().tolist()))); f.write('\n')
