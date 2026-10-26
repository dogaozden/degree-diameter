import math
exec(open('pick.py').read().split('# many')[0])
few = [x for x in rows if 1 <= x[4] <= 3 and x[5] == 1 and x[0] <= 2540]
few.sort(key=lambda x: (x[4], x[0]))
for x in few[:40]: print("FEW N=%d m=%d k=%d r=%d inv=%d g=%d" % x)
print(len(few))
