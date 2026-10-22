#!/usr/bin/env bash
# usage: finish.sh SOLUTION d D TABLE "group description"
# Rebuilds the Haar graph independently (build_haar.py), runs bigcheck, and on VALID saves the record files.
set -eu
sol=$1; d=$2; D=$3; table=$4; gdesc=$5
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
N=$(head -1 "$sol" | awk '{for(i=1;i<=NF;i++) if($i=="N") print $(i+1)}')
n=$((2*N))
spec=$(head -1 "$sol" | awk '{s=""; for(i=3;i<=NF && $i!="n";i++) s=s $i "_"; print s "x" $(i+1)}')
tmp=/tmp/claude-0/g; mkdir -p $tmp
python3 "$here/build_haar.py" "$sol" $tmp/d${d}D${D}_$n.edges.txt
/tmp/claude-0/bc/bigcheck -t 1 $tmp/d${d}D${D}_$n.edges.txt $d $D > "$here/runs/bigcheck_d${d}D${D}_$n.txt" || true
tail -1 "$here/runs/bigcheck_d${d}D${D}_$n.txt"
grep -q "^VALID" "$here/runs/bigcheck_d${d}D${D}_$n.txt" || { echo "NOT VALID"; exit 1; }
R=$root/records/bipartite_dd/d${d}D${D}; mkdir -p $R
B=$n-frontier-haar-$spec
gzip -c $tmp/d${d}D${D}_$n.edges.txt > $R/$B.edges.txt.gz
cp "$sol" $R/$B.solution.txt
sha=$(sha256sum $tmp/d${d}D${D}_$n.edges.txt | cut -d' ' -f1)
moore=$(python3 -c "print(f'{2*sum(($d-1)**i for i in range($D)):,}')")
cat > $R/README.md <<EOT
# ($d,$D): $(printf "%'d" $n) vertices (table $(printf "%'d" $table))

Table value: $(printf "%'d" $table) (Miller–Širáň DS14v2 Table 4 = CombinatoricsWiki, March 2013; the live wiki could not
be read from the container, see research/frontier/TABLE.md). Bipartite Moore bound $moore.

Construction (frontier-opus, $(date +%F)): Haar graph H(G,S) of G = $gdesc (order $N): vertices (g,A), (g,B);
edges (g,A) ~ (s g, B), s ∈ S, |S| = $d. $d-regular, sides $N + $N. S is in $B.solution.txt (matrices over GF(p),
up to sign for PSL / up to scalars for PGL; meta(a,j) = element (a,j) of Z_m ⋊_r Z_k; z = element of the cyclic factor).
Found by research/frontier/haar_gen.c (annealing over S with targeted moves).
Rebuild: \`python3 research/frontier/build_haar.py records/bipartite_dd/d${d}D${D}/$B.solution.txt out.edges.txt\`
(re-implements the group independently of the C search; also checks both eccentricities by BFS).

File: $B.edges.txt.gz — plain edge list, first line n, then "u v" per line; side A = 0..$((N-1)), side B = $N..$((n-1)).
sha256 of the uncompressed file: $sha

Checked $(date +%F) with research-lab/verify/bigcheck (independent checker, BFS from every vertex):
$(tail -1 "$here/runs/bigcheck_d${d}D${D}_$n.txt") (research/frontier/runs/bigcheck_d${d}D${D}_$n.txt).
EOT
echo "saved $R/$B"
