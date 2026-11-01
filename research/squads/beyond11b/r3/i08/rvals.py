import sys
def rof(p,k):
    # return smallest r>=2 with multiplicative order exactly k mod p
    for r in range(2,p):
        x=1; ok=True
        for i in range(1,k+1):
            x=x*r%p
            if x==1 and i<k: ok=False; break
        if ok and x==1: return r
    return None
for p,k in [(7,3),(50003,31),(1613,31),(39,13),(13,3),(26941,29),(929,29),(155,31),(31,5),(6773,13),(521,13),(55,11),(11,5),(19091,17),(1123,17),(57,19),(19,3),(18431,7),(2633,7),(41,5)]:
    pass
pairs=[(7,3),(1613,31),(13,3),(929,29),(31,5),(521,13),(11,5),(1123,17),(19,3),(2633,7),(67,3),(307,17)]
for p,k in pairs: print(p,k,rof(p,k))
