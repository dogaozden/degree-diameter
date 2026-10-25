# Octonion model of H(11) with G2(2)-symmetry of the 756 set (job cell-14-7, third session; a negative probe)

The E7 root lattice is the lattice of imaginary integral octonions. A frame of 7 mutually orthogonal E7 roots
(e7frame.py) splits the other 112 roots into (±f_a ± f_b ± f_c ± f_d)/2 over the 7 complements of Fano lines, so the
frame carries an octonion multiplication (octo.py: 16 of the 2^7 line orientations are alternative). octohex.c builds
the split Cayley hexagon of that algebra over F_11 (points: singular imaginary octonions; lines: 2-spaces with product
0) in hexgen.c's file format. In this model:
- the W(E7) orbits on points are the same seven (756, 10080, 12096, 15120, 30240, 48384, 60480), and the 756 orbit R*
  is pairwise opposite (octo_setup.py);
- H = {w in W(E7) : w fixes u0 and preserves the product} has order 96 for every orientation (= |G2(2)| / 126), and
  H maps hexagon lines to lines. So H is a group of hexagon automorphisms fixing R* and the Hermitian spread S*
  (the 1,332 lines in u0^perp) (octo_h.py, octo_setup.py);
- H-orbits: on R* 12, 12, 12, 48, 48, 48 and six of 96; on S* 12, 24, three of 48 and twelve of 96; on the 76,608
  candidate points 802 orbits, of which 44 are pairwise opposite (six of size 32, 38 of size 96) (octo_orbits.py).

Why it does not help: for an H-invariant extension (one extra orbit H·x with lines H·L), the type condition of the
mirrored surgery becomes, for every base orbit O and its image orbit O', the exact equality of two subsets of H up to
translation: {h : h^-1 r0 in N(x)} = c·{h : h^-1 s0 in N(L)}. These are random-looking subsets of about 8 of the 96
elements of H, so no pair matches. Also R* has three 12-orbits and S* only one, so a fully equivariant f does not exist
without dropping 24 base points. Symmetry turns the count condition into an exact one; it only helps if the
neighbourhoods themselves are structured (unions of cosets), which they are not here.
