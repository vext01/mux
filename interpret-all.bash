#!/bin/bash 
#
# this is a comment
#
echo "interpretation-stage: "

FILES="$(ls *.out)"

for f in $FILES; 
do 
  g=${f%.out}
  ./mux-interpretation.bash $g
done
