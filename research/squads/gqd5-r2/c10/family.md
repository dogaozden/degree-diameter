# Explicit partial ovoids of W(q), q odd: torus-orbit family, size 3q-1

Coordinates as in gqlib.W(q): points of PG(3,q), w(x,y) = x0y2 + x1y3 - x2y0 - x3y1, collinear iff w = 0.
Dot product on F_q^2: u.v = u0v0 + u1v1; perp: v^perp = (-v1, v0), so u.v^perp = 0 iff u = v projectively.

## Definition (q >= 5)
- a_1 = (1,0), a_2 = (0,1), a_3 = (1,1); b_i = a_{i-1}^perp (indices mod 3), so b_1 = (-1,1), b_2 = (0,1), b_3 = (-1,0).
- Orbit O_i = { (a_i, c b_i) : c in F_q^* }, q-1 points each (i = 1,2,3). These are the orbits of the torus
  diag(t,t,1,1) (a similitude, w(gx,gy) = t w(x,y)) through the points (a_i, b_i).
- Extra points: (x, 0) with x = (1,t), t not in {0,1}; and (0, z^perp) with z not in {a_1,a_2,a_3,x} and x.z^perp != 0.
  These lie on the totally isotropic lines {x2=x3=0} and {x0=x1=0}.
- S(q) = O_1 u O_2 u O_3 u {the two extra points}, |S(q)| = 3(q-1)+2 = 3q-1.

## Proof that S(q) is a partial ovoid
For P = (a, c b) and P' = (a', c' b') (vectors a, a', b, b' in F_q^2, c, c' in F_q^*),
  w(P,P') = [a0 c' b'0 + a1 c' b'1] - [c b0 a'0 + c b1 a'1] = c'(a.b') - c(b.a').
Note a.b' = 0 iff b' = a^perp iff a = b'^perp, and b.a' = 0 iff a' = b^perp.

1. Inside O_i: w = (c'-c)(a_i.b_i), and a_i.b_i = a_i.a_{i-1}^perp != 0 because a_i != a_{i-1}. Distinct c give non-collinear points.
2. O_i versus O_j (i != j): w = 0 needs c'(a_i.b_j) = c(b_i.a_j) with c, c' nonzero. Here a_i.b_j = 0 iff a_i = a_{j-1},
   and b_i.a_j = 0 iff a_j = a_{i-1}. Since a_1, a_2, a_3 are distinct, for each pair {i,j} exactly one of these holds
   (for j = i+1 the first holds and the second needs a_{i+1} = a_{i-1}, false; the other order is symmetric).
   So one side of the equation is 0 and the other is nonzero, and no c, c' in F_q^* solve it.
3. (x,0) versus O_i: w = c (x.b_i) (with P = (a_i, c b_i) as the second point); this is 0 iff b_i = x^perp iff a_{i-1} = x.
   Excluded because x is not one of a_1, a_2, a_3.
4. (0,y) versus O_i, y = z^perp: w = -(y.a_i), 0 iff a_i = y^perp = z. Excluded because z is not in {a_1,a_2,a_3}.
5. (x,0) versus (0,y): w = x.y != 0 by choice.
Hence no two points of S(q) are collinear. Existence of x, z for q >= 5: PG(1,q) has q+1 >= 6 points, x needs t in F_q\{0,1},
and z needs one of the q+1-4 >= 2 remaining points. For q = 3 the extra points do not exist; O_1 u O_2 u O_3 (size 6) is the family.

## Maximality inside the torus-invariant class (why 3 orbits is the limit)
Every torus-invariant set off L_A u L_B is a union of orbits O(a,b) (a, b in PG(1,q)), and w-collinearity between
O(a,b) and O(a',b') with a.b != 0 requires exactly one of a.b' = 0, b.a' = 0 for the pair to be a partial ovoid. Viewing
i -> j when a_i.b_j = 0 gives a tournament on the chosen orbits; equal b-values cannot coexist (that forces an arc
inside a class, which is impossible), so the b-values are distinct, each vertex has out-degree at most 1, and a tournament
on m vertices needs m(m-1)/2 <= m, i.e. m <= 3. Points of L_A (resp. L_B) are pairwise collinear, so at most one point
from each. Hence 3(q-1)+2 = 3q-1 is the maximum over torus-invariant partial ovoids of this type.

## Verification
- family.py (gqlib.is_partial_ovoid on gqlib.W(q)): q = 5, 7, 9, 11 pass (sizes 14, 20, 26, 32); q = 3 gives 6 (orbits only).
- direct_check.py (independent w-check, no gqlib): zero collinear pairs for q = 3, 5, 7, 9, 11, 13, 17, 19 (sizes 6, 14, 20, 26, 32, 38, 50, 56).
- Compare: 2q+1 at q = 11 is 23; this family gives 32 >= 2q+1 for all q >= 5. The lab's search record for W(11) is 70 (PREAMBLE2 item 10).
  This is an explicit family, not a record, and it is far below the Tallini bound q^2-q+1 = 111.

## Scores
q = 11: 32 (family.py). Files: family.py, direct_check.py, out_small.txt, out_11.txt.
