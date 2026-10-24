"""Convert research/p4/d6/hexgen.c output (hex_q{q}.bin) to the gh_build text format ("P q", then one line of q+1
point ids per hexagon line). Usage: python3 hexbin2txt.py hex_qQ.bin > gh_Q.txt"""
import sys, struct
b = open(sys.argv[1], 'rb').read()
q, N, L = struct.unpack_from('<3i', b, 0)
ids = struct.unpack_from('<%di' % (L * (q + 1)), b, 12)
assert N == L
out = ['%d %d' % (N, q)]
for l in range(L): out.append(' '.join(map(str, ids[l * (q + 1):(l + 1) * (q + 1)])))
sys.stdout.write('\n'.join(out) + '\n')
