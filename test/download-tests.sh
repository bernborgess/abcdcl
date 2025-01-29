#!/bin/bash

cd test

instances=(
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/AIM/aim.tar.gz"
#  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/LRAN/f.tar.gz" This benchmark is too huge to run locally.
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/JNH/jnh.tar.gz"
  "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/DUBOIS/dubois.tar.gz"
  "https://homepages.dcc.ufmg.br/~bernardoborges/tests/pj1-tests.tar.gz"
)

for inst in "${instances[@]}"; do
  filename=$(basename "$inst")
  if [ ! -f "$filename" ]; then
    echo "Downloading $filename..."
    wget --no-check-certificate "$inst"
  else
    echo "$filename already exists, skipping download."
  fi
  tar xfz "$filename"
done
