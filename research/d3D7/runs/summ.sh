#!/bin/bash
# best cost per order in a liftx output file
awk '/^GROUP/{split($2,a,"=");split($7,b,"="); N=a[2]; c=b[2]+0; if(!(N in m)||c<m[N]){m[N]=c; g[N]=$4}} END{for(N in m) print N, m[N], g[N]}' "$1" | sort -n | tr '\n' ';'; echo
