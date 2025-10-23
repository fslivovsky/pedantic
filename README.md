# Pedantic DQBF Solver

A solver for Dependency Quantified Boolean Formulas (DQBF) using Counter-Example Guided Abstraction Refinement (CEGAR) with ordered decision lists.

## Overview

This solver implements a CEGAR-based approach for solving DQBF formulas in DQCIR format. It uses:
- **Decision lists** for modeling existential variable functions
- **Expansion variables** for quantifier expansion
- **SAT-based counterexample detection** and refinement

## Installation

### Requirements
- Python 3.7+
- [PySAT](https://pysathq.github.io/) library

### Setup
```bash
pip install python-sat
```

## Usage

### Basic Solving

Solve a DQBF formula:
```bash
python dqbf_solver.py formula.dqcir
```

**Exit codes:**
- `10`: Formula is SATISFIABLE
- `20`: Formula is UNSATISFIABLE
- `1`: Error or solver terminated abnormally

### Options

#### Verbose Mode
Show detailed solving progress including counterexamples, decision list state, and model functions:
```bash
python dqbf_solver.py -v formula.dqcir
```

#### Formula Information
Display formula structure without solving:
```bash
python dqbf_solver.py --info formula.dqcir
```

#### Equivalence Detection
Detect equivalent existential variables:
```bash
python dqbf_solver.py --detect-equiv formula.dqcir
```

Two existential variables are considered equivalent if they have the same dependencies and cannot be forced to different values under any assignment to their dependencies.

### Verbose Output Details

When running with `-v`, the solver displays:

1. **Counterexample details** - For each counterexample found:
   - Existential and universal variable assignments
   - Decision list state for each existential variable:
     - `no_rule_fired` variables showing position in decision list
     - `rule_fire` variables with their premises
     - `value` variables for each rule

2. **Rule additions** - When new rules are added to decision lists

3. **Model functions** (SAT results only) - The output values for all universal assignments

### Example Session

```bash
$ python dqbf_solver.py example.dqcir
INFO: Parsing example.dqcir...
INFO: Solving...
INFO: Formula is SATISFIABLE (after 3 iterations)
Result: SATISFIABLE

$ python dqbf_solver.py -v example.dqcir
INFO: Parsing example.dqcir...
DEBUG: Parsed 10 variables and gates
DEBUG: Tseitin transformation complete: 25 clauses
INFO: Solving...
DEBUG: 
=== Iteration 1 ===
DEBUG: Found potential counterexample:
DEBUG:   Existential assignment: [$y]
DEBUG:   Universal assignment: [x1, ~x2]
...
INFO: Formula is SATISFIABLE (after 3 iterations)
INFO: Computing model functions for all universal assignments:
INFO:   [~x1, ~x2] → [~$y]
INFO:   [~x1, x2] → [$y]
INFO:   [x1, ~x2] → [~$y]
INFO:   [x1, x2] → [$y]
Result: SATISFIABLE
```

## Input Format

The solver accepts DQBF formulas in DQCIR format.

### Example DQCIR File
```
#QCIR-G14
forall(x1, x2)
exists(y; x1, x2)
output(g1)
g1 = and(g2, g3)
g2 = or(y, x1)
g3 = or(-y, x2)
```