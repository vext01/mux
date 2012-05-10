#!/bin/bash 
#
# this is a comment
#
echo "lrs-stage: "

FILES="$(ls *.ine)"

for f in $FILES; 
do 
  ./run-lrs-file.bash $f
done
