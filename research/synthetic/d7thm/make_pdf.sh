#!/bin/sh
# D7_THEOREMS.md -> D7_THEOREMS.tex -> D7_THEOREMS.pdf (pandoc, then tectonic). Run from research/synthetic/.
set -e
TECTONIC=${TECTONIC:-tectonic}
pandoc D7_THEOREMS.md -s -f markdown+tex_math_dollars -t latex \
  -V geometry:margin=2.2cm -V fontsize=10pt -V documentclass=article -V colorlinks=true \
  -V header-includes='\sloppy\emergencystretch=3em\usepackage{amssymb}\usepackage{amsmath}\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.15}' \
  -o D7_THEOREMS.tex
$TECTONIC -X compile D7_THEOREMS.tex --keep-logs >/dev/null 2>&1 || $TECTONIC D7_THEOREMS.tex
