#!/bin/bash

find . -type f -name "*.cnf" ! -name "ex1.cnf" -exec rm {} +
