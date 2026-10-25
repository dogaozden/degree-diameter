# expand a <g,sigma>-super-vertex solution (indices into gsupers_<kind>.pkl) to og vertex indices
import sys, pickle
kind, solf, out = sys.argv[1], sys.argv[2], sys.argv[3]
supers = pickle.load(open(f'gsupers_{kind}.pkl', 'rb'))
chosen = [int(x) for x in open(solf).read().split() if x.strip()]
sol = sorted(v for si in chosen for v in supers[si])
with open(out, 'w') as f:
    f.write('\n'.join(map(str, sol)) + '\n')
print(kind, 'super-vertices', len(chosen), '-> orbits', len(sol))
