# Non-split coset graphs at (6,5) (job fresh-6-5): groups G of order 2n, n in [NLO, NHI], and classes of
# involutions t with <t> core-free and NOT complemented by a normal subgroup of index 2 (the complemented case is
# an orbit-symmetric Haar graph, scanned by scan_orbit.g). Exports B(G; <t>, <t>) for bicoset.c.
# usage: gap -q -c 'NLO:=343;; NHI:=360;; OUTDIR:="../bc/nonsplit";; MAXGROUPS:=1500;;' bicoset.g scan_nonsplit.g
for n in [NLO..NHI] do
    m := 2 * n;
    if NrSmallGroups(m) > MAXGROUPS then Print("SKIPORDER ", m, " ", NrSmallGroups(m), "\n"); continue; fi;
    for i in [1..NrSmallGroups(m)] do
        G := SmallGroup(m, i);
        idx2 := Filtered(NormalSubgroups(G), N -> Index(G, N) = 2);
        j := 0;
        for c in ConjugacyClasses(G) do
            t := Representative(c);
            if Order(t) <> 2 then continue; fi;
            L := Group(t);
            if Size(Core(G, L)) > 1 then continue; fi;
            if ForAny(idx2, N -> not t in N) then continue; fi;
            j := j + 1;
            lab := Concatenation("ns_n", String(n), "_g", String(m), "_", String(i), "_t", String(j));
            r := ExportBicoset(G, L, L, Concatenation(OUTDIR, "/", lab, ".tmp"), lab);
            Exec(Concatenation("mv ", OUTDIR, "/", lab, ".tmp ", OUTDIR, "/", lab, ".txt"));
            Print("EXPORT ", lab, " ", StructureDescription(G), " orbits=", r[3], "\n");
        od;
    od;
od;
Print("ALLDONE\n");
QUIT;
