#!/bin/bash

find . -type f -name "*.cnf" ! -name "ex*.cnf" -exec rm {} +
find out/ -type f -not -name '*.minisat_output' -exec rm {} \;
