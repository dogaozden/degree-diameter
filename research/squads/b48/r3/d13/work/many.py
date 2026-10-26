import math
exec(open('pick.py').read().split('# many')[0])
many = [x for x in rows if x[2] >= 4 and x[2] % 2 == 0 and x[1] % 2 == 1 and pow(x[3], x[2]//2, x[1]) == x[1]-1 and x[5] == 1 and x[0] <= 2530]
many.sort(key=lambda x: x[0])
for x in many: print("MANY N=%d m=%d k=%d r=%d inv=%d g=%d" % x)
print(len(many))
