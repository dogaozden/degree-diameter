# export dc2 files (|H| = 2, non-Haar H only) for the SEMIDIRECT products G = C3 : P, P = SmallGroup(PORD, id),
# P acting on C3 by inversion through an index-2 subgroup K (x acts trivially iff x in K). One file set per (id, K).
# usage: gap -q -c 'PORD:=256; IDS:=[...]; OUTDIR:="d";' sdp_export.g
SKIPHAAR := true;
Read("dc2_lib.g");
SDPExport := function(PORD, id, OUTDIR)
  local C, A, inv, P, kidx, K, f, G;
  C := CyclicGroup(IsPermGroup, 3);
  A := AutomorphismGroup(C);
  inv := First(AsList(A), a -> Order(a) = 2);
  P := SmallGroup(PORD, id);
  kidx := 0;
  for K in Filtered(NormalSubgroups(P), N -> Index(P, N) = 2) do
    kidx := kidx + 1;
    f := GroupHomomorphismByFunction(P, A, function(x) if x in K then return One(A); else return inv; fi; end);
    G := SemidirectProduct(P, f, C);
    G := Image(IsomorphismPermGroup(G));
    ExportPairs(G, 2, Concatenation(OUTDIR, "/sdp", String(PORD), "_", String(id), "_", String(kidx)));
  od;
end;
for id in IDS do
  SDPExport(PORD, id, OUTDIR);
od;
QUIT;
