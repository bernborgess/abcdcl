#!/bin/bash
cd test
cargo build -q 2>/dev/null
cargo run -q -- ex1.cnf 2>/dev/null

benchmarks=(
  "f" # all SAT
#   "dubois" # all UNSAT
#   "aim" # 48 SAT, 24 UNSAT
#   "jnh" # 16 SAT, 24 UNSAT
)

for bm in "${benchmarks[@]}"; do
    if [ -f "${bm}.tar.gz" ]; then
        echo -e "\n\nRunning ${bm} benchmark"
        for file in ${bm}*.cnf; do
            echo "Running $file..."
            cargo run -q -- "$file" 2>/dev/null
        done
    else
        echo -e "\n${bm}*.tar.gz not found."
    fi
done
