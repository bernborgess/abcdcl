#!/bin/bash

cd test
wget http://minisat.se/downloads/MiniSat_v1.14_linux -O minisat
chmod +x minisat
./minisat -h