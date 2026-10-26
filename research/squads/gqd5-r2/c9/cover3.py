import json, sys
N = {2:7, 3:13, 4:21, 5:31}
CAPM = {5:7, 4:10, 3:6, 2:11}
def feasible(cnt):
    tot = sum(cnt.values())
    if tot == 1: return True
    if tot > 11: return False
    return all(cnt[s] == 0 or tot <= CAPM[s] for s in cnt)
best = {}
for c5 in range(0,8):
  for c4 in range(0,11):
    for c3 in range(0,7):
      for c2 in range(0,12):
        cnt = {5:c5,4:c4,3:c3,2:c2}
        tot = c5+c4+c3+c2
        if tot == 0 or not feasible(cnt): continue
        K = c5*31 + c4*21 + c3*13 + c2*7
        if K not in best or tot < sum(best[K].values()):
            best[K] = {str(s):v for s,v in cnt.items() if v>0}
M = 122
while (M+1) in best: M += 1
print("contiguous up to", M, "first gap", M+1)
print([(k, best[k]) for k in range(123, M+6) if k in best])
json.dump({str(k): best[k] for k in range(123, M+1)}, open('plan_d8_ext.json','w'), indent=0)
