# invariants of split metacyclic groups from runs/cands.txt (lines: m k r N key); output runs/inv_<part>.txt
L := SplitString(StringFile("/home/user/degree-diameter/research/squads/deep-49/r1/c2/runs/cands.txt"), "\n");
P := Filtered(L, x -> Length(x) > 0);
lo := Int(Sum([]) + 0);
