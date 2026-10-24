#!/bin/bash
cd /home/user/degree-diameter/research/cell147/units
./do_cell.sh d7D7 ../data/gh_5.txt 6 1 9 && ../apsp cells/d7D7.edges 7 7 > cells/d7D7.apsp.txt
./do_cell.sh d9D7 ../data/gh_7.txt 6 1 9 && ../apsp cells/d9D7.edges 9 7 > cells/d9D7.apsp.txt
./do_cell.sh d10D7 ../data/gh_8.txt 6 1 9 && ../apsp cells/d10D7.edges 10 7 > cells/d10D7.apsp.txt
./do_cell.sh d11D7 ../data/gh_9.txt 6 1 9 && ../apsp cells/d11D7.edges 11 7 > cells/d11D7.apsp.txt
./do_cell.sh d12D7 ../data/gh_9.txt 6 2 9 && ../apsp cells/d12D7.edges 12 7 > cells/d12D7.apsp.txt
