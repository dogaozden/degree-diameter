# G = F_7^2 : K (affine, as permutations of the 49 points) for every class of subgroups K of GL(2,7) with |K| = 12h,
# h in HS; exports dc2 files (core-free subgroups of order h, Haar-type skipped) to OUTDIR/aff_<h>_<k>_<i>_<j>.dc2.
# N = 2|G|/h = 1176 for every such pair.
Read("dc2_lib.g");
SKIPHAAR := true;
F := GF(7); vecs := Elements(F^2);
transl := PermList(List(vecs, v -> Position(vecs, v + [One(F), Zero(F)])));
Ks := List(ConjugacyClassesSubgroups(GL(2, 7)), Representative);
for h in HS do
  cand := Filtered(Ks, K -> Size(K) = 12 * h);
  Print("h = ", h, ": ", Length(cand), " classes of K\n");
  for k in [1..Length(cand)] do
    K := cand[k];
    gens := List(GeneratorsOfGroup(K), M -> PermList(List(vecs, v -> Position(vecs, v * M))));
    G := Group(Concatenation(gens, [transl]));
    if Size(G) <> 49 * Size(K) then Print("size mismatch\n"); fi;
    ExportPairs(G, h, Concatenation(OUTDIR, "/aff_", String(h), "_", String(k)));
    Print("  K ", k, " ", StructureDescription(K), "\n");
  od;
od;
QUIT;
