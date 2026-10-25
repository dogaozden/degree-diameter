# tohex.py VERTFILE OUTFILE : map vertex ids (9*i+t) to H(8) point ids and write one id per line
import sys
ids = [int(x) for x in open('/home/user/degree-diameter/research/squads/d10D7-r5/c3/vert_h8ids.txt').read().split()]
vs = [int(x) for x in open(sys.argv[1]).read().split()]
hs = [ids[v] for v in vs]
assert len(set(hs)) == len(hs)
open(sys.argv[2], 'w').write('\n'.join(map(str, hs)) + '\n')
print('mapped', len(hs), 'vertices')
