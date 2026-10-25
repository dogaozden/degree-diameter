import collections
exec(open('dbg2.py').read().split("print(\"unreached total\"")[0])
# collinear with base point 0 = points sharing a line with 0
coll0 = set()
for j in point_lines[0]:
    coll0.update(lines[j])
coll0.discard(0)
bad_coll = sum(1 for x in pts_unreached if x//6 in coll0 and (x%6)%2==0)
bad_self = sum(1 for x in pts_unreached if x//6 == 0)
bad_far = sum(1 for x in pts_unreached if x//6 not in coll0 and x//6 != 0 and (x%6)%2==0)
print("source point 0: unreached colour-0 point sheets: collinear", bad_coll, " far", bad_far, " self", bad_self)
print("collinear points (70) each have one length-2 walk; far points: 10 geodesics")
