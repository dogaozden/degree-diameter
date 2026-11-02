import math, random
from collections import defaultdict
from screend import walk_vals, pred, NSL, P
random.seed(3)
S=[(0,1)]+[(random.randrange(P), random.choice((1,-1))) for _ in range(6)]
print("S",S)
v=walk_vals(S)
print("random-S H-marginal pred holes", round(pred(v),1), "min W/N", round(min(v)/NSL,2), "zeros", sum(1 for x in v if x==0))
