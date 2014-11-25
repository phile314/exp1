#!/bin/sh

lualatex presentation.tex
bibtex presentation.aux
lualatex presentation.tex
lualatex presentation.tex

