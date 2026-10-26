import sys
sys.argv = [sys.argv[0], sys.argv[1]]
exec(open('/home/user/degree-diameter/research/squads/b48/r1/c18/check_edges.py').read().split('for u in range(4)')[0])
tot = 0
for z in range(n):
    c, _ = ecc_far(z)
    tot += c
print("sum far over all z:", tot, "unordered:", tot // 2)
