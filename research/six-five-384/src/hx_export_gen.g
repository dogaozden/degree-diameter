# Generic export for orders other than 384 (job six-five-384, orders 401-450). For each id in IDS of order ORD:
# abelian groups -> line "ABELIAN ORD id" (bounded separately: at most 542 vertices, job fresh-6-5);
# r2 = rank of G/G'G^2 >= 5 -> line "RANK ORD id r2" (excluded, see README);
# otherwise write DIR/pc_ORD_id.txt (solvable: compact pc format for hxexpand) or DIR/hx_ORD_id.txt (full table),
# via a temporary file renamed when complete, and print "EXPORTED ORD id".
# usage: gap -q -A -c 'ORD:=420;; IDS:=[1..41];; DIR:="q";;' hx_export_gen.g
for id in IDS do
  K := SmallGroup(ORD, id);
  if IsAbelian(K) then Print("ABELIAN ", ORD, " ", id, "\n"); continue; fi;
  r2 := Number(AbelianInvariants(K), x -> x mod 2 = 0);
  if r2 >= 5 then Print("RANK ", ORD, " ", id, " ", r2, "\n"); continue; fi;
  srt := AsSSortedList(K);
  e := One(K);
  elms := Concatenation([e], Filtered(srt, x -> x <> e));
  pos := List(srt, x -> Position(elms, x));
  idx := x -> pos[PositionSorted(srt, x)] - 1;
  A := AutomorphismGroup(K);
  gens := GeneratorsOfGroup(A);
  tmp := Concatenation(DIR, "/tmp_", String(ORD), "_", String(id));
  out := OutputTextFile(tmp, false); SetPrintFormattingStatus(out, false);
  if IsSolvableGroup(K) and CanEasilyComputePcgs(K) then
    pcgs := Pcgs(K); pre := "pc_";
    AppendTo(out, Length(elms), " ", Length(pcgs), "\n");
    for g in pcgs do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(x * g))), " "), "\n"); od;
    for x in elms do AppendTo(out, JoinStringsWithSeparator(List(ExponentsOfPcElement(pcgs, x), String), " "), "\n"); od;
  else
    pre := "hx_";
    AppendTo(out, Length(elms), "\n");
    for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(idx(a * b))), " "), "\n"); od;
  fi;
  AppendTo(out, Length(gens), "\n");
  for g in gens do AppendTo(out, JoinStringsWithSeparator(List(elms, x -> String(idx(Image(g, x)))), " "), "\n"); od;
  CloseStream(out);
  Exec(Concatenation("mv ", tmp, " ", DIR, "/", pre, String(ORD), "_", String(id), ".txt"));
  Print("EXPORTED ", ORD, " ", id, "\n");
od;
QUIT;
