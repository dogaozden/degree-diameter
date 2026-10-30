#!/bin/bash
# make_meta_record.sh K NAME m k r u t v "S" SEARCH_EDGES SEARCH_OUT "DESCRIPTION": record files for a self-dual Haar graph
# of the metacyclic group <x, y | x^m = y^k = 1, y x y^-1 = x^r> (beta(x) = x^u, beta(y) = x^t y^v): formula edge list,
# apsp at D = 5 and D = 4, independent Python check, Cayley build + nauty comparison with the search's own edge list,
# and a rebuild script records/build_<NAME>.sh.  Run from research/selfdual-d5/.
K=$1; NAME=$2; m=$3; k=$4; r=$5; u=$6; t=$7; v=$8; S="$9"; SE=${10}; SO=${11}; DESC=${12}
E=records/$NAME.edges
python3 records/build_metacyclic_haar.py $m $k $r "$S" $E 5 || exit 1
{ ./src/apsp $E $K 5; ./src/apsp $E $K 4 | tail -1; } > records/${NAME}_apsp.txt
python3 ../beyond-haar-d5/records/check_independent.py $E $K 5 > records/${NAME}_check_independent.txt
python3 records/build_metacyclic_cayley.py $m $k $r $u $t $v "$S" /tmp/${NAME}_cayley.edges 5 > records/${NAME}_cayley.txt
python3 src/canon_eq.py $E /tmp/${NAME}_cayley.edges $SE >> records/${NAME}_cayley.txt
[ -n "$SO" ] && cp $SO records/${NAME}_search.out
sha=$(sha256sum $E | cut -d' ' -f1)
cat > records/build_$NAME.sh <<EOB
#!/bin/bash
# Rebuild and check $NAME (run from research/selfdual-d5/).  $DESC
# Haar graph of G = <x, y | x^$m = y^$k = 1, y x y^-1 = x^$r>, elements x^i y^j written (i,j), S = {$S}, (g,A) ~ (s g, B).
# Self-dual: psi(g) = beta(g)^-1 with beta(x) = x^$u, beta(y) = x^$t y^$v maps S to itself, so the graph is also a Cayley
# graph of G : <tau> (tau g tau = beta(g)) with T = S tau.
S="$S"
python3 records/build_metacyclic_haar.py $m $k $r "\$S" /tmp/$NAME.edges 5        # GAP-free build + BFS from every vertex
gcc -O2 -o /tmp/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
/tmp/apsp /tmp/$NAME.edges $K 5 | tail -1; /tmp/apsp /tmp/$NAME.edges $K 4 | tail -1
python3 ../beyond-haar-d5/records/check_independent.py /tmp/$NAME.edges $K 5
cmp /tmp/$NAME.edges records/$NAME.edges && echo "identical to the saved edge list"
sha256sum records/$NAME.edges     # $sha
python3 records/find_beta_meta.py $m $k $r "\$S"                                    # includes: $u $t $v
python3 records/build_metacyclic_cayley.py $m $k $r $u $t $v "\$S" /tmp/${NAME}_cayley.edges 5
python3 src/canon_eq.py records/$NAME.edges /tmp/${NAME}_cayley.edges
EOB
chmod +x records/build_$NAME.sh
echo "sha256 $sha"; cat records/${NAME}_apsp.txt | tail -2; tail -2 records/${NAME}_check_independent.txt; cat records/${NAME}_cayley.txt
