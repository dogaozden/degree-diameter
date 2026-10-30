# b4a2y validation against b4a2x (../../beyond-haar-d5/exh/b4a2x.c)

Both programs search all lifts of the base [[2,3],[3,2]] for diameter 5; b4a2y uses more symmetry and a different
loop order, so it reports fewer (equivalent) solutions. Compared by nauty canonical forms (sol2g6.py | nauty-labelg):

- SmallGroup(72,30) = C3 x ((C6 x C2) : C2), both runs exhaustive: b4a2x 25,740 solutions in 1,331 s, b4a2y 3,481
  solutions in 190 s. Isomorphism classes: 362 and 362, the same set (comm of the sorted canonical graph6 lines is
  empty both ways).
- SmallGroup(90,6) = C15 x S3: b4a2x (previous job, stopped in its first branch) 16 solutions = 2 classes; b4a2y
  exhaustive, 7 solutions in 265 s = the same 2 classes. So these are all the 360-vertex lifts of this base by this
  group up to isomorphism.
- Groups of order 92-94 that b4a2x finished (C23:C4, D92, C31:C3, D94): no solution in either program.
