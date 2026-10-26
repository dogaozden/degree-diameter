import sys
sys.path.insert(0,'/home/user/degree-diameter/research/squads/own-small/r1/e2/work')
from s6 import decode2
import os
src='/home/user/degree-diameter/research/squads/own-small/r1/e2/census/Sparse6'
out='/home/user/degree-diameter/research/squads/own-small/r1/e2/bases'
for name,f,ln in [('CAT_6','CAT_6.s6',0),('CAT_8','CAT_8.s6',0),('CAT_14','CAT_14.s6',0),('CAT_16','CAT_16.s6',0),('CAT_18','CAT_18.s6',0),('CAT_20','CAT_20.s6',1),('CAT_24','CAT_24.s6',0),('CAT_26','CAT_26.s6',0),('CAT_30','CAT_30.s6',0),('CAT_32','CAT_32.s6',0),('CAT_38','CAT_38.s6',0),('CAT_40','CAT_40.s6',0),('CAT_42','CAT_42.s6',0),('CAT_54','CAT_54.s6',0),('CAT_64','CAT_64.s6',0)]:
    lines=open(os.path.join(src,f)).read().splitlines()
    n,E=decode2(lines[ln])
    with open(os.path.join(out,name+'.txt'),'w') as o:
        o.write(f"{n} {len(E)}\n")
        for a,b in E: o.write(f"{a} {b}\n")
    print(name,n,len(E))
