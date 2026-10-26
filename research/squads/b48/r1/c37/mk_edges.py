import sys
# usage: mk_edges.py N "a0,a1,a2,a3" "b0,b1,b2,b3" OUT.edges  (graph x_A ~ (a_i x + b_i mod N)_B, B vertex = N + y)
N = int(sys.argv[1]); a = [int(t) for t in sys.argv[2].split(',')]; b = [int(t) for t in sys.argv[3].split(',')]
with open(sys.argv[4], 'w') as f:
    f.write(f"{2*N}\n")
    for x in range(N):
        for i in range(4):
            f.write(f"{x} {N + (a[i]*x + b[i]) % N}\n")
