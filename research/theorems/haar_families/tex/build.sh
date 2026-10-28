#!/bin/bash
# Build HAAR_FAMILIES.tex and .pdf from the Markdown master (pandoc + tectonic). Usage: build.sh [path-to-tectonic]
set -e
cd "$(dirname "$0")"
T=${1:-tectonic}
python3 md2tex_filter.py ../../HAAR_FAMILIES.md filtered.md
pandoc filtered.md -s -o HAAR_FAMILIES.tex -H header.tex -V documentclass=article -V fontsize=10pt \
  -V title="Uniform families in the shape of the D = 8–10 Haar records" -V date="2026-10-27 (draft)"
"$T" HAAR_FAMILIES.tex
