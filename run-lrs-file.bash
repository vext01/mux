#!/bin/bash 
#
# this is a comment
#
echo "lrs-file: "
InFile=$1
OutFile=${1%ine}out
echo $InFile

lrs $InFile $OutFile
