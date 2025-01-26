#!/bin/bash
cd test 2>/dev/null
cargo build -q 2>/dev/null

# Define ANSI color codes
GREEN="\033[0;32m"
GREEN_BG="\033[0;42m"
RED="\033[0;31m"
RED_BG="\033[0;41m"
RESET="\033[0;0m"

# Initialize counters
pass_count=0
total_count=0

# Check if ./minisat exists
if [ ! -f "./minisat" ]; then
    echo "Error: ./minisat not found. Did you run \"./test/download-minisat.sh\"?"
    exit 1
fi

benchmarks=(
#    "f" # all SAT -> f benchmark is too huge, can't run locally.
   "dubois" # all UNSAT
   "aim" # 48 SAT, 24 UNSAT
   "jnh" # 16 SAT, 24 UNSAT
)

for bm in "${benchmarks[@]}"; do
    if [ -f "${bm}.tar.gz" ]; then
        echo -e "\n\nRunning ${bm} benchmark"
        for file in ${bm}*.cnf; do
            # echo "Running $file..."
            abcdcl_outfile="./out/${file}.output"
            cargo run -q -- "$file" > "$abcdcl_outfile" 2>error.log
            if [ $? -ne 0 ]; then
                echo "Error: cargo run failed for $file. Stopping script."
                echo -e "\n====================================================\n"
                cat error.log
                echo -e "\n====================================================\n"
                exit 1
            fi
            abcdcl_tail=$(tail "$abcdcl_outfile" -n 1)

            # minisat for comparison
            minisat_outfile="./out/${file}.minisat_output"

            # Run minisat if the output file doesn't exist
            if [ ! -f "$minisat_outfile" ]; then
                ./minisat "$file" "$minisat_outfile" &>/dev/null
            fi
            minisat_head=$(head "$minisat_outfile" -n 1)

            # Increment total count
            total_count=$((total_count + 1))


            # Check that first line is the same
            if [ "$minisat_head" == "$abcdcl_tail" ]; then
                echo -e "${GREEN_BG}PASS${GREEN} $file${RESET}"
                pass_count=$((pass_count + 1))
            else
                echo -e "${RED_BG}FAIL${RED} $file: expected $minisat_head got $abcdcl_tail${RESET}"
            fi
        done
    else
        echo -e "\n${bm}*.tar.gz not found."
    fi
done

# Report final results
echo -e "\n\nSummary:"
echo -e "Passed $pass_count / ${total_count} tests."
