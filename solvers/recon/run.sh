#!/usr/bin/env bash

#---------------------------------
# CoRe Challenge 2022
# solver execution script
#
# Input:
#  col file (as $1)
#  dat file (as $2)
# Output:
#  as in https://core-challenge.github.io/2022/#example-of-output
#---------------------------------

# please specify your solver command so that one can execute it by
# "$ /2022solver/run.sh xxx.col yyy.dat"

if [ -z "$1" ] || [ ! -r "$1" ] || [ -z "$2" ] || [ ! -r "$2" ]
then
  echo "usage: run.sh xxx.col yyy.dat"
  exit 1
fi

/2022solver/recon_th "$1" "$2"

# out="$(dirname "$2")/$(basename "$2" .dat).out"
# /usr/bin/time -v /2022solver/recon_th "$1" "$2" 2>&1 | tee "${out}"
