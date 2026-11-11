#!/bin/bash
# record_best.sh ORB_A ORB_B : build G + orbits (A-side bases in global B ids, B-side bases in global A ids), check with apsp,
# and if valid save graphs/d17D5_n<n>_orbit_bases.txt, .edges.gz and .check.txt
cd "$(dirname "$0")/.."
cat "$1" "$2" > /tmp/rb_bases.txt
python3 graphs/build_d17D5_hubs.py /tmp/rb.edges --orbits /tmp/rb_bases.txt | tail -2
r=$(bin/apsp /tmp/rb.edges 17 5 | tail -1); echo "$r"
n=$(head -1 /tmp/rb.edges)
if echo "$r" | grep -q "RESULT VALID"; then
  cp /tmp/rb_bases.txt graphs/d17D5_n${n}_orbit_bases.txt
  gzip -c /tmp/rb.edges > graphs/d17D5_n${n}_orbits.edges.gz
  { bin/apsp /tmp/rb.edges 17 5; echo "edge list sha256 $(sha256sum /tmp/rb.edges | cut -c1-64)";
    echo "orbits: $(wc -l < $1) with N in B (A-hubs), $(wc -l < $2) with N in A (B-hubs); 22 hubs each";
    echo "rebuild: python3 research/squads/beyond-small/graphs/build_d17D5_hubs.py OUT.edges --orbits research/squads/beyond-small/graphs/d17D5_n${n}_orbit_bases.txt"; } > graphs/d17D5_n${n}.check.txt
  echo "saved n=$n"
fi
