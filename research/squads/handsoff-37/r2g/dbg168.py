import sys
sys.argv = ['x']
exec(open('calib168.py').read().split("comp = Comp(S, [0], [0])")[0])
comp = Comp(S, [0], [0])
from collections import Counter
print('far of conder168 itself', far_count(n, N))
print(Counter((len(e[4]), e[2], e[3]) for e in comp.edges))
print([ (len(e[4]), e[2], e[3]) for e in comp.edges if e[2]==3 and e[3]==3][:5])
