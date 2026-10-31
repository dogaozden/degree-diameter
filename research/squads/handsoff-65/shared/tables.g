# Multiplication tables of all non-abelian groups of order NLO..NHI (identity first), one file per group, for
# invhaar.c. usage: gap -q -c 'NLO:=343;; NHI:=360;; OUTDIR:="../bc/tab";; MAXGROUPS:=400;;' tables.g
if not IsBound(MAXGROUPS) then MAXGROUPS := 100000; fi;
for n in [NLO..NHI] do
    if NrSmallGroups(n) > MAXGROUPS then Print("SKIPORDER ", n, "\n"); continue; fi;
    for i in [1..NrSmallGroups(n)] do
        K := SmallGroup(n, i);
        if IsAbelian(K) then continue; fi;
        elms := AsSSortedList(K); e := One(K);
        elms := Concatenation([e], Filtered(elms, x -> x <> e));
        lab := Concatenation("t_n", String(n), "_i", String(i));
        fn := Concatenation(OUTDIR, "/", lab);
        out := OutputTextFile(Concatenation(fn, ".tmp"), false); SetPrintFormattingStatus(out, false);
        AppendTo(out, n, "\n");
        for a in elms do AppendTo(out, JoinStringsWithSeparator(List(elms, b -> String(Position(elms, a * b) - 1)), " "), "\n"); od;
        CloseStream(out);
        Exec(Concatenation("mv ", fn, ".tmp ", fn, ".txt"));
        Print("TABLE ", lab, " ", StructureDescription(K), "\n");
    od;
od;
Print("ALLDONE\n");
QUIT;
