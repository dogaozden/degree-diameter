# export dc2 files (|H| = 2, non-Haar H only) for G = C3 x SmallGroup(PORD, i), i in IDS; usage:
# gap -q -c 'PORD:=256; IDS:=[...]; OUTDIR:="d";' c3p_export.g
SKIPHAAR := false;
Read("dc2_lib.g");
for id in IDS do
  G := DirectProduct(CyclicGroup(3), SmallGroup(PORD, id));
  G := Image(IsomorphismPermGroup(G));
  ExportPairs(G, 2, Concatenation(OUTDIR, "/c3p", String(PORD), "_", String(id)));
od;
QUIT;
