import struct, sys
# verify that each flag (p, l) has p on l in hex_q11.bin (LP: N lines x (q+1) point ids after a 3-int32 header)
path, flagf = sys.argv[1], sys.argv[2]
with open(path, 'rb') as f:
    q, N, L = struct.unpack('<iii', f.read(12))
    LP = struct.unpack('<%di' % (N * (q + 1)), f.read(4 * N * (q + 1)))
bad = 0; cnt = 0
for line in open(flagf):
    p, l = map(int, line.split()); cnt += 1
    if p not in LP[l * (q + 1):(l + 1) * (q + 1)]:
        bad += 1
print(f"{flagf}: flags={cnt} not_on_line={bad}")
