# c09 holes anatomy, D = 8, (19,8) hole classes

Setup: haar_big0 ORBIT="3 6 1", K=8, THREADS=1. Alpha = conj by g = [[0,-1],[1,-1]], z -> r z (r of order 3 mod n).
Holes listed with EVAL=best UNCPRINT=1. Classifier: c09/classify.py (sign-invariant tests: alpha-fixed = g M g^-1 = +-M
and z = 0; torus = commutes with g; order of M mod +-I; trace^2 mod p).

## State 1: psl 79 x Z181 (seed 1, 720 s), N = 44,612,880, best cost 3 (reached at t = 26 s, no gain in 690 s)
Holes (3 total, all A side):
- (16,10;58,61) z=99: tr = -2, order 79 (unipotent), z != 0
- (28,14;10,53) z=36: tr = 2, order 79 (unipotent), z != 0
- (39,58;65,42) z=46: tr = 2, order 79 (unipotent), z != 0
Classes: 3 x {z != 0, not alpha-fixed, not in torus of g, unipotent (trace +-2, order p)}. None is an involution,
order 3, or a torus element; no z = 0 holes.

## State 2: sl 113 x Z31 (seed 2, 300 s), N = 44,726,304, best cost 3 (reached early, no gain in 300 s)
Holes (3 total, all A side):
- (72,90;106,87) z=14: order 57 (mod +-I), z != 0
- (80,7;31,79) z=8: order 57 (mod +-I), z != 0
- (110,82;23,49) z=9: order 57 (mod +-I), z != 0
Classes: 3 x {z != 0, not alpha-fixed, not in torus of g}; traces in the output of the classifier are the non-square
trace class (tr^2 not 0, 1, 4). Elements of order 57 lie in a non-split torus of SL(2,113).

## Reading
Both stalled states have exactly 3 holes, all with z != 0 and none alpha-fixed. The holes are not z = 0 layer
elements and not involutions. In state 1 they are unipotent (order p), which lie in no torus of g. In state 2 they lie in
non-split tori of order 57. A fix would target the z != 0, non-alpha-fixed layer: e.g. a move that changes the generator
orbit that covers the unipotent cosets (a random walk from the uncovered element was already in TARGP). The count of 3 is
the same in both states, which suggests a structural obstruction of the orbit form (the orbit of a unipotent/torus
element under alpha has size 3 and the holes come in alpha-orbits of size 3), not random noise.

## Correction and check (added after the first write)
- Matching holes up to sign (PSL) and the z map z -> r z: in both states the 3 holes form ONE alpha-orbit.
  State 2: z = 14 -> 8 -> 9 -> 14 under r = 5 (order 3 mod 31), matrices permuted by alpha.
  State 1: r = 48 (order 3 mod 181); z cycle 46 -> 36 -> 99 -> 46 with matrices (39,58;65,42) -> (28,14;10,53) -> (16,10;58,61)
  (alpha of each matrix equals the next one up to PSL sign). So the three holes are one alpha-orbit. Traces: state 2 all 46 (tr^2 = 82 mod 113), order 57.
- So cost 3 = one uncovered alpha-orbit (3 elements, energy 3/3 = 1). The search is stuck with exactly one bad orbit.
