#!/bin/sh
# Offline build using an existing TeX Live distribution. No shell escape.
set -eu
cd "$(dirname "$0")"
mkdir -p tex-cache/formats tex-cache/var render
export TEXINPUTS=".:/usr/share/texmf/tex//:/usr/share/texlive/texmf-dist/tex//:/etc/texmf/tex//:"
export TFMFONTS="/usr/share/texmf/fonts/tfm//:/usr/share/texlive/texmf-dist/fonts/tfm//:"
export T1FONTS="/usr/share/texmf/fonts/type1//:/usr/share/texlive/texmf-dist/fonts/type1//:"
export ENCFONTS="/usr/share/texmf/fonts/enc//:/usr/share/texlive/texmf-dist/fonts/enc//:"
export TEXFONTMAPS="/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:"
export TEXMFVAR="$PWD/tex-cache/var"
if [ ! -f tex-cache/formats/pdflatex.fmt ]; then
  pdftex -ini -etex -no-shell-escape -interaction=nonstopmode -halt-on-error \
    -jobname=pdflatex -progname=pdflatex -output-directory=tex-cache/formats \
    pdflatex.ini > tex-cache/format-build.log 2>&1
fi
for paper_pass in 1 2; do
  pdflatex -fmt=tex-cache/formats/pdflatex.fmt -no-shell-escape \
    -interaction=nonstopmode -halt-on-error manuscript.tex > "render/pass${paper_pass}.log" 2>&1
done
