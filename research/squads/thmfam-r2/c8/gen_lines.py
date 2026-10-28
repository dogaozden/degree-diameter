# Writes "a b c d z" generator lines for H(PGL(2,q), psi(S_p)) from our own psi (Definition 2.2), z = 0 (m = 1).
import sys
import qlib as L
p, q = int(sys.argv[1]), int(sys.argv[2])
x, y = L.xy_solutions(q)[0]
assert (x*x + y*y + 1) % q == 0
for al in L.lps_set(p):
    a, b, c, d = L.psi(al, x, y, q)
    print(a, b, c, d, 0)
print("# x=%d y=%d" % (x, y), file=sys.stderr)
