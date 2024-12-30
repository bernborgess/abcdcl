# Atila - Bernardo - CDCL(T) SAT Solver

This project implements a **Conflict-Driven Clause Learning (CDCL)** SAT solver with support for the **two-watched literals** optimization. The solver reads input in DIMACS CNF format and outputs whether the formula is satisfiable or unsatisfiable, along with a satisfying assignment if one exists.

## Features

- **Conflict-Driven Clause Learning (CDCL)**: Efficiently solves SAT problems using clause learning and non-chronological backjumping.
- **Two-Watched Literals**: Optimized unit propagation for improved performance.
- **DIMACS CNF Input/Output**: Supports standard SAT solver input and output formats.
- **Optional Features**:
  - Variable selection using the **VSIDS heuristic**.
  - Restart strategies (e.g., **Luby sequence**).

## Input Format

The solver accepts a text file in **DIMACS CNF format**, which consists of:

1. Comment lines starting with `c`.
2. A problem line starting with `p`, specifying the number of variables and clauses.
3. Clauses as space-separated integers, ending with `0`.

Example:

```
c Example DIMACS file
p cnf 3 2
1 -2 3 0
-1 2 0
```

## Output Format

The output consists of two lines:

1. The first line is `s SATISFIABLE` or `s UNSATISFIABLE`.
2. If satisfiable, the second line is `v M`, where `M` is a space-separated list of literals in the satisfying assignment.

Example (if satisfiable):

```
s SATISFIABLE
v 1 -2 3
```

Example (if unsatisfiable):

```
s UNSATISFIABLE
```

## Usage

1. Place your DIMACS CNF file (e.g., `input.cnf`) in the project directory.
2. Run the solver with:
   ```
   TODO...
   ```
3. View the output in the terminal.

## Testing

You can test the solver using benchmark files from the [SATLIB](http://www.satlib.org/) repository. To compare performance, you may also use the **MiniSat** solver.

## Performance Comparison

- Measure runtime (in milliseconds) on a selection of benchmarks.
- Compare results with MiniSat on the same input files.
- Report the timeout value, hardware specifications, and runtime data.

## References

- **DIMACS Format**: [DIMACS CNF Format](http://www.satcompetition.org/2009/format-benchmarks2009.html)
- **SATLIB Benchmarks**: [SATLIB Repository](http://www.satlib.org/)
- **Key Papers**:
  - Moskewicz et al., *Chaff: Engineering an Efficient SAT Solver* (2001).
  - Silva and Sakallah, *GRASP: A Search Algorithm for Propositional Satisfiability* (1996).

## License

This project is licensed under the MIT License. See `LICENSE` for more details.
