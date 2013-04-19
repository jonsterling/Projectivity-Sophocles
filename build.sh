#!/bin/sh

lhs2tex Analyze.lhs > Analyze.tex
xelatex Analyze.tex
open Analyze.pdf
