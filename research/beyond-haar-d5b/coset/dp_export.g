# usage: gap -q -c 'K:=65; PORD:=32; IDS:=[1..51]; OUTDIR:="d";' dp_export.g
# bi-coset data (.dc2, H = K classes only) for G = C_K x SmallGroup(PORD, j), j in IDS, core-free H of order 2.
Read("dc2_lib.g");
for j in IDS do
  G := DirectProduct(CyclicGroup(K), SmallGroup(PORD, j));
  G := Image(IsomorphismPermGroup(G)); G := Image(SmallerDegreePermutationRepresentation(G));
  ExportPairs(G, 2, Concatenation(OUTDIR, "/dp", String(K), "x", String(PORD), "_", String(j)));
od;
QUIT;
