#!/usr/bin/env bash

GREEN='\033[0;32m'
YELLOW='\033[0;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

color()(set -o pipefail;"$@" 2> >(sed $'s,.*,\e[31m&\e[m,'>&2))
#color()(set -o pipefail;"$@" 2> >(sed $'s,.*,\e[31m&\e[m,'>&2))

benchmark_lists="
  list/list-1st-benchmark.csv
  list/list-2nd-benchmark.csv
  list/list-3rd-benchmark.csv
"

files=0
missing=0
correct=0
error=0

# shellcheck disable=SC2034
for benchmark_list in $benchmark_lists
do
  while read -r job
  do
    files=$((files+1))
    graph=$(echo "$job" | cut -f 1 -d',')
    dat=$(echo "$job" | cut -f 2 -d',')
    if [ ! -r "${graph}" ]
    then
      echo "graph file '${graph}' is not readable"
      exit
    fi
    if [ ! -r "${dat}" ]
    then
      echo "dat file '${dat}' is not readable"
      exit
    fi

    out="$(dirname "${dat}")/$(basename "${dat}" .dat).out"
    out="${out//benchmark/solutions}"
    if [ ! -r "${out}" ]
    then
      echo -e "${YELLOW}out file '${out}' is missing"
      missing=$((missing+1))
    else
      echo "running validator: ${graph} -> ${dat}: ${out}"

      # check if source and target state are the same (sometimes not sorted in
      # dat files)
      dat_source="$(grep "^s" "${dat}" | tr -d '\n\r' | cut -d' ' -f 2- | xargs -n1 | sort -n | xargs)"
      dat_target="$(grep "^t" "${dat}" | tr -d '\n\r' | cut -d' ' -f 2- | xargs -n1 | sort -n | xargs)"
      out_source="$(grep "^s" "${out}" | tr -d '\n\r' | cut -d' ' -f 2- | xargs -n1 | sort -n | xargs)"
      out_target="$(grep "^t" "${out}" | tr -d '\n\r' | cut -d' ' -f 2- | xargs -n1 | sort -n | xargs)"
      if [ "${dat_source}" != "${out_source}" ]
      then
        echo "Files are not consistent"
        echo "${dat_source}"
        echo "${out_source}"
        exit
      fi
      if [ "${dat_target}" != "${out_target}" ]
      then
        echo "Files are not consistent"
        echo "${dat_target}"
        echo "${out_target}"
        exit
      fi
      echo -en "${GREEN}"
      if ! color ./isr-validator.py "${graph}" "${dat}" "${out}"
      then
        error=$((error+1))
      else
        correct=$((correct+1))
      fi
    fi
    echo -e "${NC}"
  done < "${benchmark_list}"
done

echo -e "${files}: ${GREEN}${correct}${NC}/${YELLOW}${missing}${NC}/${RED}${error}${NC}"
