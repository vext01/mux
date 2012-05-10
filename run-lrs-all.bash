#!/bin/sh 

echo "lrs-stage: "

FILES="$(ls *.ine)"

for f in $FILES; 
do 
  ./run-lrs-file.bash $f
done
