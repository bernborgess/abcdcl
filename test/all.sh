#!/bin/bash

# Move to the test directory and build the project
cd test 2>/dev/null
cargo build -q 2>/dev/null

# Prepare output caching
mkdir -p out/pj1-tests/{unsat,sat}

# Define ANSI color codes
GREEN="\033[0;32m"
GREEN_BG="\033[0;42m"
YELLOW="\033[0;33m"
YELLOW_BG="\033[0;43m"
RED="\033[0;31m"
RED_BG="\033[0;41m"
RESET="\033[0;0m"

# Define timeout in seconds
TIMEOUT=60
echo -e "Running tests with timeout of ${TIMEOUT}s"

# Check if ./minisat exists
if [ ! -f "./minisat" ]; then
    echo "Error: ./minisat not found. Did you run \"./test/download-minisat.sh\"?"
    exit 1
fi

# Used for quick debugging
# MINISAT_USE_CACHE=true

# Define test sets
benchmarks=("dubois" "aim" "jnh")
folders=("pj1-tests/sat" "pj1-tests/unsat")

# Initialize global counters
global_pass_count=0
global_total_count=0

echo -e "\n\nRunning benchmarks and test folders...\n"

# Main test loop: Benchmarks + Test Folders
for test_set in "${benchmarks[@]}" "${folders[@]}"; do
    # Identify test type (benchmark or folder)
    if [[ " ${benchmarks[*]} " =~ " ${test_set} " ]]; then
        test_type="benchmark"
    else
        test_type="folder"
    fi

    # Initialize per-test-set counters
    pass_count=0
    fail_count=0
    timeout_count=0
    total_count=0
    abcdcl_total_time=0
    minisat_total_time=0

    echo -e "\nRunning ${test_set} ($test_type)..."

    # Loop through CNF files
    if [ "$test_type" == "benchmark" ]; then
        file_pattern="${test_set}*.cnf"
    else
        file_pattern="${test_set}/*.cnf"
    fi

    for file in $file_pattern; do
        # Skip if no files match
        if [ ! -f "$file" ]; then
            continue
        fi

        # Define output files
        abcdcl_outfile="./out/${file%.cnf}.abcdcl.out"
        minisat_outfile="./out/${file%.cnf}.minisat.out"

        # Run ABCDCL and measure time
        start_time=$(date +%s%3N)
        timeout $TIMEOUT cargo run -q -- "$file" > "$abcdcl_outfile" 2>error.log
        exit_code=$?
        end_time=$(date +%s%3N)
        abcdcl_time=$((end_time - start_time))

        if [ $exit_code -eq 124 ]; then # TIMEOUT
            echo -e "${YELLOW_BG}TIME${YELLOW} $file took too long${RESET}"
            timeout_count=$((timeout_count + 1))
            total_count=$((total_count + 1))
            continue
        elif [ $exit_code -ne 0 ]; then
            echo -e "${RED_BG}FAIL${RED} $file: error code $exit_code${RESET}"
            cat error.log
            fail_count=$((fail_count + 1))
            total_count=$((total_count + 1))
            continue
        fi

        # Normalize ABCDCL output to `SAT` or `UNSAT`
        abcdcl_head=$(head -n 1 "$abcdcl_outfile" | sed 's/s SATISFIABLE/SAT/; s/s UNSATISFIABLE/UNSAT/')

        # Run MiniSat and measure time
        if [ "$MINISAT_USE_CACHE" = true ] && [ -f "$minisat_outfile" ]; then
            minisat_time=0
        else
            start_time=$(date +%s%3N)
            ./minisat "$file" "$minisat_outfile" &>/dev/null
            end_time=$(date +%s%3N)
            minisat_time=$((end_time - start_time))
        fi

        minisat_head=$(head -n 1 "$minisat_outfile")

        # Update counters
        total_count=$((total_count + 1))
        abcdcl_total_time=$((abcdcl_total_time + abcdcl_time))
        minisat_total_time=$((minisat_total_time + minisat_time))

        if [ "$minisat_head" == "$abcdcl_head" ]; then
            echo -e "${GREEN_BG}PASS${GREEN} $file${RESET}"
            pass_count=$((pass_count + 1))
        else
            echo -e "${RED_BG}FAIL${RED} $file: expected $minisat_head got $abcdcl_head${RESET}"
            fail_count=$((fail_count + 1))
        fi
    done

    # Compute averages
    if [ "$total_count" -gt 0 ]; then
        avg_abcdcl_time=$((abcdcl_total_time / total_count))
        avg_minisat_time=$((minisat_total_time / total_count))
    else
        avg_abcdcl_time=0
        avg_minisat_time=0
    fi

    # Print LaTeX-compatible summary
    echo -e "${test_set} & ${avg_abcdcl_time} & ${avg_minisat_time} & ${pass_count} / ${fail_count} / ${timeout_count} / ${total_count} \\\\\\\\" >> results.tex

    # Update global counters
    global_pass_count=$((global_pass_count + pass_count))
    global_total_count=$((global_total_count + total_count))
done

# Print final summary
echo -e "\n===================================================="
echo -e "Total tests: $global_total_count"
echo -e "Passed: $global_pass_count"
echo -e "Failed: $((global_total_count - global_pass_count))"
echo -e "===================================================="

# Exit with appropriate status
if [ $global_pass_count -ne $global_total_count ]; then
    exit 1
else
    exit 0
fi
