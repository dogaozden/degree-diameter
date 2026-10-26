# h03: orbit representatives of voltage triples (a, b, c) on the 2+2 cubic base under simultaneous conjugation.
# Tree edges (0, 2, 3) are 0. Conjugation by s maps every voltage x -> s x s^-1, which is an isomorphism of the lift,
# so a is a class rep, b ranges over C(a)-orbit reps, c over (C(a) n C(b))-orbit reps. a = 0 is skipped (double edge).
# Writes eval lines "0 a 0 0 b c" to stdout; prints the number of lines on stderr.
import sys, numpy as np
fn = sys.argv[1]
N = int(np.fromfile(fn, dtype=np.int32, count=1)[0])
T = np.fromfile(fn, dtype=np.uint16, offset=4).reshape(N, N).astype(np.int64)
inv = np.array([int(np.where(T[x] == 0)[0][0]) for x in range(N)])
C = T[T, inv[:, None]]          # C[x,g] = x g x^-1
reps_a = np.unique(C.min(axis=0))
out = []
allc = np.arange(N)
for a in reps_a:
    if a == 0: continue
    Ca = allc[T[a, :] == T[:, a]]                       # centralizer of a
    canon_b = C[Ca, :].min(axis=0)                      # min over h in C(a) of h b h^-1, for each b
    for b in np.unique(canon_b):
        Cab = Ca[T[b, Ca] == T[Ca, b]]                  # C(a) n C(b)
        canon_c = C[Cab, :].min(axis=0)
        for c in np.unique(canon_c):
            out.append(f"0 {a} 0 0 {b} {c}")
sys.stdout.write("\n".join(out) + "\n")
print(f"N={N} a-reps={len(reps_a)} lines={len(out)}", file=sys.stderr)
