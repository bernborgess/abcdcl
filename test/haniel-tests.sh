#!/bin/bash

# Move to the test directory and build the project
cd test 2>/dev/null
cargo build -q 2>/dev/null

# Define ANSI color codes
GREEN="\033[0;32m"
GREEN_BG="\033[0;42m"
YELLOW="\033[0;33m"
YELLOW_BG="\033[0;43m"
RED="\033[0;31m"
RED_BG="\033[0;41m"
RESET="\033[0;0m"

# Define timeout in seconds
TIMEOUT=300
echo -e "Running tests with timeout of ${TIMEOUT}s"

# Initialize counters
pass_count=0
total_count=0

# Check if ./minisat exists
if [ ! -f "./minisat" ]; then
    echo "Error: ./minisat not found. Did you run \"./test/download-minisat.sh\"?"
    exit 1
fi

# Define the test directories
folders=(
    "pj1-tests/sat"
    "pj1-tests/unsat"
)

# Loop through each folder
for folder in "${folders[@]}"; do
    # Check if the folder exists
    if [ ! -d "$folder" ]; then
        echo "Warning: Test folder $folder does not exist. Skipping."
        continue
    fi
    # Loop through each .cnf file in the folder
    for file in "$folder"/*.cnf; do

# # Test cases with BAD dimacs comment
# failed_tests=(
#     "pj1-tests/sat/sat10.cnf"
#     "pj1-tests/sat/sat12.cnf"
#     "pj1-tests/unsat/false.cnf"
# )

# for file in "${failed_tests[@]}"; do

        # Skip if no .cnf files are found
        if [ ! -f "$file" ]; then
            continue
        fi

        # Define output files
        abcdcl_outfile="${file%.cnf}.abcdcl.out"
        minisat_outfile="${file%.cnf}.minisat.out"

        # Run the program with the test file
        timeout $TIMEOUT cargo run -q -- "$file" > "$abcdcl_outfile" 2>error.log
        exit_code=$?  # Capture the exit code immediately
        if [ $exit_code -eq 124 ]; then
            echo -e "${YELLOW_BG}TIMEOUT${YELLOW} $file took too long${RESET}"
            total_count=$((total_count + 1))
            continue
        elif [ $exit_code -ne 0 ]; then
            echo -e "${RED_BG}FAIL${RED} $file: error code $exit_code${RESET}"
            echo -e "\n====================================================\n"
            cat error.log
            echo -e "\n====================================================\n"
            continue
            # exit 1
        fi

        # Get the last line of the program's output
        abcdcl_head=$(head "$abcdcl_outfile" -n 1)

        # Run minisat if the output file doesn't exist
        if [ ! -f "$minisat_outfile" ]; then
            ./minisat "$file" "$minisat_outfile" &>/dev/null
        fi

        # Get the first line of minisat's output
        minisat_head=$(head "$minisat_outfile" -n 1)

        # Increment total count
        total_count=$((total_count + 1))

        # Compare the outputs
        if [ "$minisat_head" == "$abcdcl_head" ]; then
            echo -e "${GREEN_BG}PASS${GREEN} $file${RESET}"
            pass_count=$((pass_count + 1))
        else
            echo -e "${RED_BG}FAIL${RED} $file: expected $minisat_head got $abcdcl_head${RESET}"
        fi
    done
done

# Print summary
echo -e "\n===================================================="
echo -e "Total tests: $total_count"
echo -e "Passed: $pass_count"
echo -e "Failed: $((total_count - pass_count))"
echo -e "===================================================="

# Exit with the appropriate status
if [ $pass_count -ne $total_count ]; then
    exit 1
else
    exit 0
fi
