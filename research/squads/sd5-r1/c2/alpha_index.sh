#!/bin/bash
# alpha_index.sh FILE.ht REC: map an sdk record number (ALPHA and EXT lines counted) to the ALPHA index used by tabu6.
awk -v R="$2" 'BEGIN{r=0;a=0;ok=0} /^(ALPHA|EXT)/{ if (r==R) { if ($1=="ALPHA") { print a; ok=1 } else { print "EXT"; ok=1 } exit } if ($1=="ALPHA") a++; r++ } END{ if(!ok) print "NONE" }' "$1"
