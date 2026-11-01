#!/bin/bash
# savelift.sh SOL m k r D TAG [deg]: copy a salift_s/salift4 solution over Z_m x|_r Z_k to sols/TAG.sol (with a header
# comment), rebuild the lift with sol2edges.py, check it all-pairs with apsp at D and D-1 (checks/TAG.apsp.txt), and
# put the gzipped edge list and the check into research/frontier/beyond/graphs/.
set -e
H=$(cd "$(dirname "$0")/.." && pwd); sol=$1; m=$2; k=$3; r=$4; D=$5; tag=$6; deg=${7:-3}
G="$H/../beyond/graphs"; tmp="$H/runs/tmp_${tag:?}.edges"
cp "$sol" "$H/sols/$tag.sol"
sed -i "1i # $tag: degree-$deg lift; base edges 'u v x' over Z$m x|_$r Z$k (index a*$k+j, (a,j)(b,l) = (a + $r^j b mod $m, j + l mod $k)); build: tools/sol2edges.py SOL $m $k $r OUT" "$H/sols/$tag.sol"
python3 "$H/tools/sol2edges.py" "$H/sols/$tag.sol" $m $k $r "$tmp" > /dev/null
{ "$H/bin/apsp" "$tmp" $deg $D; echo "at D = $((D - 1)):"; "$H/bin/apsp" "$tmp" $deg $((D - 1)) | tail -1; } > "$H/checks/$tag.apsp.txt"
gzip -c "$tmp" > "$G/$tag.edges.gz"; cp "$H/checks/$tag.apsp.txt" "$G/"
rm -f -- "$tmp"
cat "$H/checks/$tag.apsp.txt"
