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

# haar5x (exhaustive valency-5 Haar graphs, diameter 5)

- SmallGroup(150,5) = (C5 x C5) : S3: with the Aut-orbit restriction on a, 288 solutions in 1.1 s; with no
  automorphisms (empty generator file, so every 4-subset {a, b, c, d} is tested), 3,000 solutions in 9.2 s. Both
  give the same single isomorphism class (nauty). One solution: apsp VALID, 300 vertices.

# b4a2y on a group with solutions, against b4a2x

- SmallGroup(96,17) (a group with solutions): b4a2x, stopped at a 3,000 s cap on a loaded machine, found 12
  solutions (runs/val_b4a2x_96_17.sol), all in one isomorphism class; b4a2y (exhaustive, 53 s) found 2 solutions in
  one class, the same one (nauty canonical forms equal).
