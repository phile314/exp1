#!/bin/sh

lualatex presentation.tex
#bibtex presentation.aux
biber presentation
lualatex presentation.tex
lualatex presentation.tex

