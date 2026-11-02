# deep-37: an Opus-led deep pass on the bipartite (3,7) cell

Session on branch `claude/deep-37-d3d7-c59pr7`, Nov 1-2 2026, 22:39Z to __END__. Goal: a bipartite graph with
maximum degree 3, diameter 7 and more than 168 vertices (170 is the natural target). Brief: go deep on the leads of the
hands-off Haiku run (handsoff-37): the far-46 insertion basin, the non-free F21 symmetry, the D5 family at far 60.

## Result

__RESULT__

## 1. A new exact tool: orbdfs

`src/orbdfs.c` enumerates every G-invariant cubic bipartite graph of diameter <= 7 on a given G-set (any permutation
group G; vertex stabilisers and colour-reversing elements allowed). It generalises the Oct 27 job's jsearch (free
cyclic groups only):
- orbits of vertices are discovered in BFS order from a root orbit; the representative of the earliest discovered
  orbit with a free half-edge is filled next, by edge orbits (double cosets) in a canonical order;
- an untouched orbit is relabelled freely by the G-equivariant maps of that orbit (N_G(H)/H acting on G/H), so the
  first edge into a new orbit only needs one representative per class (the gauge); untouched orbits of the same type
  are interchangeable;
- pruning: collisions(v) = (#non-backtracking walks of even length <= 6 from v) - (#distinct endpoints) never
  decreases as edges are added, and a cubic graph on 2m vertices has diameter <= 7 iff collisions(v) <= 127 - m at
  every vertex (42 at n = 170);
- two exclusions proved in the notes: non-faithful G-sets, and the twin lemma (a non-identity colour-preserving
  automorphism fixing every vertex of one side creates twins; a vertex with a twin sees at most 65 < 85 vertices of
  its side within distance 6).

Validation: identical isomorphism classes to a brute-force enumerator (`src/brute_ginv.py`) on 13 small G-sets
(S3 free and non-free, D5, colour-reversing C4, D5 and F20; diameters 5, 7, 13). Knuth estimates with PROBE=N.
G-sets come from GAP (`src/gsets.g`: every admissible orbit structure of a group on n vertices).

## 2. Lead (b): the F21 symmetry at 168, done exactly

The hands-off SAT encoding of the F21 class did not solve the 168 calibration in 9 minutes; its symmetric annealer
found a solution in 3 s. orbdfs exhausts the same class (r2f's G-set: on side A three orbits of size 7 with stabiliser
C3 and three regular orbits, on side B four regular orbits) in 8.5 s (619k nodes): 96 solutions in **two**
isomorphism classes:
- C168.1 (|Aut| = 504, girth 12, arc-transitive), 24 solutions;
- **a new (3,7) graph on 168 vertices**, 72 solutions: girth 8, Aut = AGammaL(1,8) = (C2)^3 : (C7 : C3) =
  SmallGroup(168,43), vertex orbits 56 (stabiliser C3), 28 (C6) and 84 (C2), so neither vertex- nor edge-transitive
  and not in the cubic censuses. apsp: VALID at D = 7, INVALID at D = 6. File
  `records/n168_new_girth8_aut168.edges` (sha256 in the .sha256 file). It ties the record; it does not beat it.

Both graphs have 12 edge orbits in this G-set and the closest pair (one of each class) differs in exactly 3 edge
orbits, i.e. three double cosets swapped. So the 168 record is not unique, and the hub structure (vertices fixed by an
element of order 3) supports at least two different extremal graphs.

Why F21 does not carry over to 170: an element of order 7 acts freely, and 7 does not divide 170. More generally, at
n = 170 every automorphism group has order 2^a 3^b 5^c with c <= 1 (primes >= 11 excluded by the Oct 27 job; 7 and 25
cannot act freely), and elements of order 3 must fix vertices (85 = 1 mod 3).

## 3. Lead (c): the D5 family at far 60

- Both far-60 graphs of handsoff-37 (r3a and r3b's fresh seed 56; not isomorphic) have a larger automorphism group
  than the D5 they were searched in: F20 = C5 : C4 of order 20, whose elements of order 4 swap the two colour classes
  (their squares are the D5 involutions, 3 fixed vertices per side). Their 60 far pairs are all same-side at distance 8,
  between vertices of regular orbits, in 5 classes under F20 (10 under D5); the size-5 "hub" orbits are fully covered.
- Exact: there is no F20-invariant (3,7) graph at 170 with colour-reversing C4 for any orbit structure
  (a orbits of size 20 and b of size 10, 2a + b = 17): b = __F20REV__ settled, none.
- Exact: the far-60 family's own G-set (D5, three orbits of size 5 and seven of size 10 on each side): __D5FAR60__.

So the far-60 graphs are not near a diameter-7 graph of their symmetry type: the type has none.

## 4. Reduction to minimal groups at 170

If Aut(G) contains an element of order 5 (generating P = C5, free at 170) and Aut(G) != P, then Aut(G) contains a
minimal overgroup M of P: P normal in M with |M:P| prime (M = C10, D5 or C15), or M = K:P with K a minimal P-invariant
{2,3}-subgroup, which is elementary abelian of order 2^4 or 3^4 (SmallGroup(80,49), SmallGroup(405,15)). The last
cannot act at 170 (a 3-group vertex stabiliser in a connected cubic graph has order <= 3, so orbits have size >= 135).
Hence settling every G-set of D5, C10, C15 and (C2)^4:C5 settles every (3,7) graph on 170 vertices with an
automorphism of order 5 and more than 5 automorphisms. Status: __MINSTATUS__

## 5. Lead (a): the far-46 basin

- `src/insert.c` (exhaustive pair insertion with bit-parallel scoring) reproduces handsoff c1's floors on C168.1:
  over all 31,626 two-edge insertions the best far is 46 (reached by 252 of them); over all three-edge insertions 48.
- Why 46: C168.1 is uniformly loaded. From each vertex, 53 same-side vertices are at distance 6: 18 with one geodesic,
  27 with two, 8 with three. Every one of the 252 edges is the only geodesic for exactly 36 same-side pairs at distance
  6. Removing two edges loses 72 pairs; the detour through the new pair (a - y - x - b) is 2 longer, so a lost pair comes
  back only if one end lies near the other removed edge. The best geometry (removed edges 5-6 apart) recovers 30, and
  4 pairs at the new vertices stay far: 72 - 30 + 4 = 46. Any design that removes edges of C168.1 pays 36 per edge.
- The new 168 graph is a worse seed: its edges carry 60 or 80 unique geodesics each, and its best 2-edge insertion
  gives far 96.
- "Designed" neighbourhoods: with one inserted pair the design space is exactly the 2- and 3-edge insertions, now
  exhausted; the squad card c2 tried designs plus repair (below).

## 6. Squad rounds (Haiku)

__SQUAD__

## 7. Spend and the Opus/Haiku split

__SPEND__

## 8. Comparison with the hands-off run on the same cell

__COMPARE__
