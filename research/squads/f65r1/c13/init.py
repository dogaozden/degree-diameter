import sys
sys.path.insert(0,'/home/user/degree-diameter/research/squads/f65r1/c13')
from build import *
S=[(0,1,6),(1,3,2),(1,5,5),(1,2,6),(1,3,1),(1,4,5),(1,2,2)]
lines=build_lines(S)
lnp=matching(lines)
with open('/home/user/degree-diameter/research/squads/f65r1/c13/init_sig.txt','w') as f:
    f.write("\n".join(str(x) for x in lnp)+"\n")
with open('/home/user/degree-diameter/research/squads/f65r1/c13/lines.txt','w') as f:
    for L in lines: f.write(" ".join(map(str,L))+"\n")
print("ok")
