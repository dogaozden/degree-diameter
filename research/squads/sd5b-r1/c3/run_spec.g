# usage: gap -q -c 'SPECS:=[[m, "H expression", cap, label], ...];;' run_spec.g < /dev/null
Read("/home/user/degree-diameter/research/squads/sd5b-r1/c3/build.g");
MFN := Concatenation(EXPDIR, "manifest.txt");
for sp in SPECS do
  H := EvalString(sp[2]);
  t0 := Runtime();
  L := BuildFam(sp[1], H, sp[3]);
  Print("BUILT ", sp[4], " m=", sp[1], " groups ", Length(L), " in ", Runtime()-t0, " ms\n");
  for ii in [1..Length(L)] do
    G := L[ii][1];
    tag := Concatenation("m", String(sp[1]), "_", sp[4], "_", String(ii));
    OUT := Concatenation(EXPDIR, "x_", tag, ".ht");;
    NOEXT := 1;;
    Read("/home/user/degree-diameter/research/squads/sd5b-r1/c3/export_nq.g");
    AppendTo(MFN, Size(G), " ", L[ii][2][2], " ", sp[1], " ", sp[4], " ", tag, " ", String(L[ii][3]), "\n");
    Print("EXPORTED ", tag, " order ", Size(G), " id ", L[ii][2], "\n");
  od;
od;
QUIT;
