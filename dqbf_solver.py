#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DQBF Solver Stub

A solver for Dependency Quantified Boolean Formulas (DQBF).
Uses the DQCIR parser to read formulas and provides a framework for solving.
"""

from typing import Dict, List, Set, Tuple, Optional
from pysat.solvers import Cadical195 as SAT
from dqcir_parser import DQCIRParser
from counter import Counter
import logging


class DQBFSolver:
  """Solver for Dependency Quantified Boolean Formulas."""
  
  def __init__(
    self,
    name_to_id: Dict[str, int],
    id_to_name: Dict[int, str],
    dependencies: Dict[str, List[str]],
    matrix: List[List[int]],
    universal_vars: List[str],
    output_gate_id: int,
    counter: Optional[Counter] = None
  ):
    """Initialize the DQBF solver.
    
    Args:
      name_to_id: Dictionary mapping variable/gate names to integer IDs
      id_to_name: Dictionary mapping integer IDs to variable/gate names
      dependencies: Dictionary mapping existential variables to their dependencies
             Key: existential variable name
             Value: list of universal variable names it depends on
      matrix: CNF matrix as list of clauses (each clause is a list of integers)
          Positive integers are positive literals, negative are negated
      universal_vars: List of universal variable names in order of introduction
      output_gate_id: Integer ID of the output gate that must be satisfied
      counter: Optional Counter object. If None, creates a new Counter starting from
              the maximum variable ID seen in existential vars, universal vars, and matrix.
    """
    self.name_to_id = name_to_id
    self.id_to_name = id_to_name
    self.dependencies = dependencies
    self.matrix = matrix
    self.universal_vars = universal_vars
    self.output_gate_id = output_gate_id
    
    # Create or use provided Counter object
    if counter is None:
      # Find maximum ID across all variables and matrix
      max_id = 0
      
      # Check all name_to_id mappings
      if name_to_id:
        max_id = max(max_id, max(name_to_id.values()))
      
      # Check all IDs in matrix
      for clause in matrix:
        for lit in clause:
          max_id = max(max_id, abs(lit))
      
      # Create counter starting from max_id
      self.counter = Counter(max_id)
    else:
      self.counter = counter
    
    # Derived data structures
    self.existential_vars = set(dependencies.keys())
    self.universal_var_ids = [name_to_id[v] for v in universal_vars]
    self.existential_var_ids = [name_to_id[v] for v in self.existential_vars]
    
    # Convert dependencies to ID-based mapping
    self.dependencies_by_id: Dict[int, Set[int]] = {}
    self.dependencies_by_id_list: Dict[int, List[int]] = {}
    for exist_var, deps in dependencies.items():
      exist_id = name_to_id[exist_var]
      dep_ids = [name_to_id[dep] for dep in deps]
      self.dependencies_by_id[exist_id] = set(dep_ids)
      self.dependencies_by_id_list[exist_id] = dep_ids

    # Ordered decision list structures for existential variables
    # Each existential variable has a decision list of rules
    # Rule i: if premise holds and no previous rule fired, set value to conclusion
    
    # Dictionary storing the current value variable for each existential variable
    # Key: existential variable ID, Value: current value variable ID
    self.value_vars: Dict[int, int] = {}
    
    # Dictionary storing the current "no rule fired" variable for each existential variable
    # Key: existential variable ID, Value: current "no previous rule fired" variable ID
    self.no_rule_fired_vars: Dict[int, int] = {}
    
    # Dictionary storing all rule fire variables for each existential variable
    # Key: existential variable ID, Value: current "rule fires" variable ID
    self.rule_fire_vars: Dict[int, int] = {}
    
    # List of all rule fire variables with their premises for debugging/logging
    # Each element is a tuple: (existential_var_id, fire_var_id, premise_name)
    self.all_rule_fire_vars: List[Tuple[int, int, str]] = []
    
    # List of all no_rule_fired variables with their indices for debugging/logging
    # Each element is a tuple: (existential_var_id, no_rule_fired_var_id, rule_index)
    self.all_no_rule_fired_vars: List[Tuple[int, int, int]] = []
    
    # List of all value variables with their indices for debugging/logging
    # Each element is a tuple: (existential_var_id, value_var_id, rule_index)
    self.all_value_vars: List[Tuple[int, int, int]] = []
    
    # Permanent assumptions (for fixed rule conclusions)
    self.permanent_assumptions: List[int] = []
    
    # Expansion variables: maps (existential_var_id, assignment_tuple) to expansion variable ID
    # The assignment_tuple is a tuple of literals sorted by abs(lit)
    # Key: (existential_var_id, tuple of sorted literals)
    # Value: expansion variable ID
    self.expansion_vars: Dict[Tuple[int, Tuple[int, ...]], int] = {}
    
    # Set of expansion variable IDs for quick lookup
    self.expansion_vars_set: Set[int] = set()

    self.expansion_variable_assignment: List[int] = []
    
    self.expansion_solver = SAT()
    self.counterexample_solver = SAT(bootstrap_with=matrix)
    
    # Track last counterexample for debugging (to detect if we see the same one twice)
    self.last_counterexample_existentials: Optional[Set[int]] = None
    self.last_counterexample_universals: Optional[Set[int]] = None

    for exist_var_id in self.existential_var_ids:
      self.init_model(exist_var_id)
  
  def _format_literals(self, literals: List[int]) -> str:
    """Format a list of literals with their original variable names.
    
    Args:
      literals: List of integer literals
      
    Returns:
      Formatted string like "[x1, ~x2, ...]"
    """
    parts = []
    for lit in sorted(literals, key=abs):
      var_id = abs(lit)
      var_name = self.id_to_name.get(var_id, f"id{var_id}")
      if lit > 0:
        parts.append(var_name)
      else:
        parts.append(f"~{var_name}")
    return "[" + ", ".join(parts) + "]"
  
  def init_model(self, existential_var_id: int) -> None:
    """Initialize an ordered decision list model for an existential variable.
    
    This creates the initial infrastructure for a decision list:
    1. Creates an initial value variable
    2. Creates an initial "no rule fired up to 0" variable
    3. Adds unit clause [-no_rule_fired_0] (no rule fired initially is false)
    4. Adds clause: if no_rule_fired_0 is false (i.e., we're at rule 0), 
       then existential_var should be equivalent to value_var_0
    
    Args:
      existential_var_id: The ID of the existential variable to initialize
      
    Raises:
      ValueError: If the provided ID is not an existential variable
    """
    if existential_var_id not in self.existential_var_ids:
      raise ValueError(f"Variable ID {existential_var_id} is not an existential variable")
    
    # Check if already initialized
    if existential_var_id in self.value_vars:
      return
    
    # Get the existential variable name for naming auxiliary variables
    exist_name = self.id_to_name.get(existential_var_id, f"var{existential_var_id}")
    
    # Create initial value variable (value_1)
    value_var_1 = self.counter.increase()
    self.value_vars[existential_var_id] = value_var_1
    self.id_to_name[value_var_1] = f"{exist_name}_value_1"
    
    # Add to the list of all value variables (index 1 = first value)
    self.all_value_vars.append((existential_var_id, value_var_1, 1))
    
    # Create initial "no rule fired up to 0" variable
    no_rule_fired_0 = self.counter.increase()
    self.no_rule_fired_vars[existential_var_id] = no_rule_fired_0
    self.id_to_name[no_rule_fired_0] = f"{exist_name}_nofired_0"
    
    # Add to the list of all no_rule_fired variables (index 0 = before any rules)
    self.all_no_rule_fired_vars.append((existential_var_id, no_rule_fired_0, 0))
    
    # Create "rule fires" variable for rule 1
    fires_var_1 = self.counter.increase()
    self.rule_fire_vars[existential_var_id] = fires_var_1
    self.id_to_name[fires_var_1] = f"{exist_name}_fire_1"
    
    # Add to the list of all rule fire variables (initial rule has empty premise)
    self.all_rule_fire_vars.append((existential_var_id, fires_var_1, "default"))

    # Add unit clause: no rule up to and including 0 fires
    clause1 = [no_rule_fired_0]
    self.counterexample_solver.add_clause(clause1)
    logging.debug(f"Added clause (init {exist_name}): {self._format_literals(clause1)}")
    
    # Add clauses: if no rule up to 0 fires (~no_rule_fired_0 is true, meaning no_rule_fired_0 is false),
    # then existential_var <=> value_var_0
    # equivalence: (a <=> b) = (a => b) AND (b => a) = (-a OR b) AND (a OR -b)
    clause2 = [-no_rule_fired_0, -fires_var_1, -existential_var_id, value_var_1]
    self.counterexample_solver.add_clause(clause2)
    logging.debug(f"Added clause (init {exist_name}): {self._format_literals(clause2)}")
    
    clause3 = [-no_rule_fired_0, -fires_var_1, existential_var_id, -value_var_1]
    self.counterexample_solver.add_clause(clause3)
    logging.debug(f"Added clause (init {exist_name}): {self._format_literals(clause3)}")
  
  def set_default_value(self, existential_var_id: int, value: bool) -> None:
    """Set the default value for an existential variable's decision list.
    
    This changes the current value variable to reflect the desired default.
    If value is True, the value variable remains positive.
    If value is False, the value variable becomes negative.
    
    Args:
      existential_var_id: The ID of the existential variable
      value: The default value (True or False)
      
    Raises:
      ValueError: If the variable has not been initialized with init_model
    """
    if existential_var_id not in self.value_vars:
      raise ValueError(f"Variable {existential_var_id} has not been initialized. Call init_model first.")
    
    current_value_var = self.value_vars[existential_var_id]
    self.value_vars[existential_var_id] = current_value_var if value else -current_value_var
  
  def add_rule(self, existential_var_id: int, premise: List[int], conclusion: bool, value_var: Optional[int] = None) -> None:
    """Add a new rule to the decision list for an existential variable.
    
    A rule has the form: if premise holds and no previous rule fired, set value to conclusion.
    
    This method:
    1. Creates three new variables: rule_fire_i, no_rule_fired_i, value_i
    2. Adds clauses defining rule_fire_i <=> (premise AND no_rule_fired_{i-1})
    3. Adds clauses defining no_rule_fired_i <=> (no_rule_fired_{i-1} AND NOT rule_fire_i)
    4. Adds clauses: if rule_fire_i, then existential_var <=> value_i
    5. If value_var is None: Adds value_i (or -value_i) as a permanent assumption based on conclusion
       If value_var is provided: Adds clauses defining this_value_var <=> value_var
    6. Updates the current value and no_rule_fired variables for future rules
    
    Args:
      existential_var_id: The ID of the existential variable
      premise: List of literals forming the conjunction (premise of the rule)
      conclusion: The value to assign if the rule fires (True or False)
      value_var: Optional variable ID to use for the conclusion. If provided, adds
                 equivalence clauses instead of a permanent assumption.
      
    Raises:
      ValueError: If the variable has not been initialized with init_model
    """
    if existential_var_id not in self.value_vars:
      raise ValueError(f"Variable {existential_var_id} has not been initialized. Call init_model first.")
    
    # Get current state
    previous_no_rule_fired = self.no_rule_fired_vars[existential_var_id]
    this_rule_fired = self.rule_fire_vars[existential_var_id]
    this_value_var = abs(self.value_vars[existential_var_id])
    
    # Get the existential variable name for naming auxiliary variables
    exist_name = self.id_to_name.get(existential_var_id, f"var{existential_var_id}")
    
    # Determine the rule number by parsing the current fire variable name
    # Extract rule number from name like "var_fire_N"
    current_fire_name = self.id_to_name.get(abs(this_rule_fired), "")
    try:
      rule_num = int(current_fire_name.split("_fire_")[-1]) + 1
    except (ValueError, IndexError):
      rule_num = 2  # Default to 2 if parsing fails
    
    # Create new variables
    next_rule_fired = self.counter.increase()
    this_no_rule_fired = self.counter.increase()
    next_value_var = self.counter.increase()
    
    # Add to tracking structures
    self.rule_fire_vars[existential_var_id] = next_rule_fired
    self.no_rule_fired_vars[existential_var_id] = this_no_rule_fired
    self.value_vars[existential_var_id] = next_value_var
    
    # Create a readable name for the premise
    premise_name = self._format_literals(premise) if premise else "true"
    
    # Update the name of this_rule_fired to reflect the premise it now represents
    # (it was previously the "default" but is now being used for this specific rule)
    self.id_to_name[abs(this_rule_fired)] = f"{exist_name}_fire_{rule_num - 1}_premise_{premise_name}"
    
    # Update the tracking list entry for this rule fire variable
    # Find and update the entry that had "default" as the premise
    for i, (eid, fid, pname) in enumerate(self.all_rule_fire_vars):
      if eid == existential_var_id and fid == this_rule_fired:
        self.all_rule_fire_vars[i] = (eid, fid, premise_name)
        break
    
    # Add names for the new variables
    self.id_to_name[next_rule_fired] = f"{exist_name}_fire_{rule_num}"
    self.id_to_name[this_no_rule_fired] = f"{exist_name}_nofired_{rule_num - 1}"
    self.id_to_name[next_value_var] = f"{exist_name}_value_{rule_num}"
    
    # Count how many rules exist for this existential (length of matching entries in all_rule_fire_vars)
    rule_index = sum(1 for eid, _, _ in self.all_rule_fire_vars if eid == existential_var_id)
    
    # Add the new default rule fire variable to the tracking list
    self.all_rule_fire_vars.append((existential_var_id, next_rule_fired, "default"))
    
    # Add this no_rule_fired variable to the tracking list
    self.all_no_rule_fired_vars.append((existential_var_id, this_no_rule_fired, rule_index))
    
    # Add the new value variable to the tracking list
    self.all_value_vars.append((existential_var_id, next_value_var, rule_num))
    
    # Define this_rule_fired
    for lit in premise:
      clause = [-this_rule_fired, lit]
      self.counterexample_solver.add_clause(clause)
      logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause)}")
    clause = [-lit for lit in premise] + [this_rule_fired]
    self.counterexample_solver.add_clause(clause)
    logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause)}")
    
    # Define next_no_rule_fired
    clause1 = [-this_no_rule_fired, previous_no_rule_fired]
    self.counterexample_solver.add_clause(clause1)
    logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause1)}")
    
    clause2 = [-this_no_rule_fired, -this_rule_fired]
    self.counterexample_solver.add_clause(clause2)
    logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause2)}")
    
    clause3 = [this_no_rule_fired, -previous_no_rule_fired, this_rule_fired]
    self.counterexample_solver.add_clause(clause3)
    logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause3)}")
    
    # Clause 3: if rule fires and no previous rule fired, existential_var <=> value_i
    clause4 = [-next_rule_fired, -this_no_rule_fired, -existential_var_id, next_value_var]
    self.counterexample_solver.add_clause(clause4)
    logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause4)}")
    
    clause5 = [-next_rule_fired, -this_no_rule_fired, existential_var_id, -next_value_var]
    self.counterexample_solver.add_clause(clause5)
    logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause5)}")
    
    # Clause 4: Handle conclusion based on whether value_var is provided
    if value_var is None:
      # Add value_i (or -value_i) as permanent assumption based on conclusion
      conclusion_lit = this_value_var if conclusion else -this_value_var
      self.permanent_assumptions.append(conclusion_lit)
      logging.debug(f"Added permanent assumption for {exist_name}: {self._format_literals([conclusion_lit])}")
    else:
      # Add equivalence clauses: this_value_var <=> value_var
      # (a <=> b) = (a => b) AND (b => a) = (-a OR b) AND (a OR -b)
      clause6 = [-this_value_var, value_var]
      self.counterexample_solver.add_clause(clause6)
      logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause6)}")
      
      clause7 = [this_value_var, -value_var]
      self.counterexample_solver.add_clause(clause7)
      logging.debug(f"Added clause (rule {rule_num} for {exist_name}): {self._format_literals(clause7)}")
  
  def get_expansion_variable(self, existential_var_id: int, assignment: List[int]) -> int:
    """Get or create an expansion variable for an existential variable under a universal assignment.
    
    An expansion variable represents the value of an existential variable when its dependent
    universal variables are assigned specific values. This is used in quantifier expansion.
    
    Args:
      existential_var_id: The ID of the existential variable
      assignment: List of literals (positive or negative integers) representing the assignment
                  to universal variables in the dependency set. Positive literal means True,
                  negative literal means False. Should only include variables from the dependency set.
      
    Returns:
      The ID of the expansion variable for this (existential_var, assignment) combination
      
    Raises:
      ValueError: If the existential_var_id is not valid or if assignment contains
                  variables not in the dependency set
    """
    if existential_var_id not in self.existential_var_ids:
      raise ValueError(f"Variable ID {existential_var_id} is not an existential variable")
    
    # Get the dependency set for this existential variable
    dep_set = set(self.dependencies_by_id.get(existential_var_id, []))
    
    # Verify that assignment only contains variables from the dependency set
    assignment_vars = set(abs(lit) for lit in assignment)
    if not assignment_vars.issubset(dep_set):
      extra_vars = assignment_vars - dep_set
      raise ValueError(f"Assignment contains variables not in dependency set: {extra_vars}")
    
    # Create a canonical tuple representation of the assignment
    # Sort literals by absolute value (variable ID) to ensure consistent ordering
    assignment_tuple = tuple(sorted(assignment, key=abs))
    
    # Create the key for the expansion_vars dictionary
    key = (existential_var_id, assignment_tuple)
    
    # Check if we already have an expansion variable for this combination
    if key in self.expansion_vars:
      return self.expansion_vars[key]
    
    # Create a new expansion variable
    expansion_var_id = self.counter.increase()

    # Add to id_to_name for debugging
    if existential_var_id in self.id_to_name:
      exist_name = self.id_to_name[existential_var_id]
      # Create a readable name showing the assignment
      assignment_str = "_".join(f"{abs(lit)}={'T' if lit > 0 else 'F'}" 
                                for lit in assignment_tuple)
      self.id_to_name[expansion_var_id] = f"exp_{exist_name}_{assignment_str}"
      logging.debug(f"Created expansion variable: {self.id_to_name[expansion_var_id]} (ID={expansion_var_id})")
    
    # Store the mapping
    self.expansion_vars[key] = expansion_var_id

    # Add a rule for the expansion variable
    self.add_rule(
      existential_var_id,
      premise=list(assignment),
      conclusion=True,
      value_var=expansion_var_id
    )
    
    # Add to expansion variable set
    self.expansion_vars_set.add(expansion_var_id)
    
    return expansion_var_id
  
  def get_counterexample(self) -> Tuple[bool, Optional[Tuple[List[int], List[int]]]]:
    """Get a counterexample by finding failed assumptions.
    This method:
    1. Checks if the formula is satisfiable with negated output gate
    2. If SAT, gets the satisfying assignment restricted to existential and universal vars
    3. Checks that the formula is UNSAT with this assignment and unnegated output
    4. Extracts the failed assumptions (core) from the UNSAT check
    5. Returns the failed assumptions from existential literals, and the full universal assignment
    """
    # Step 1: Try to satisfy with negated output gate, rule fire variables, and value variables
    negated_output = -self.output_gate_id
    
    # Build assumptions: negated output + permanent assumptions + rule fire vars + current value vars
    assumptions_step1 = [negated_output]
    assumptions_step1.extend(self.permanent_assumptions)
    
    # Add all rule fire variables as assumptions
    assumptions_step1.extend(self.rule_fire_vars.values())
    
    # Add all current value variables as assumptions
    assumptions_step1.extend(self.value_vars.values())

    # Add expansion variable assignment
    assumptions_step1.extend(self.expansion_variable_assignment)

    logging.debug(f"Solving with {len(assumptions_step1)} assumptions:")
    logging.debug(f"  Assumptions: {self._format_literals(assumptions_step1)}")

    result = self.counterexample_solver.solve(assumptions=assumptions_step1)
    
    if not result:
      # No counterexample found (UNSAT with negated output)
      logging.debug("No counterexample found (formula proven correct)")
      return (False, None)
    
    # Step 2: Get the satisfying assignment and restrict to existential and universal variables
    model = self.counterexample_solver.get_model()

    # Get universal and existential literals only
    counterexample_universals = [lit for lit in model if abs(lit) in self.universal_var_ids]
    counterexample_existentials = [lit for lit in model if abs(lit) in self.existential_var_ids]
    
    logging.debug(f"Found potential counterexample:")
    logging.debug(f"  Existential assignment: {self._format_literals(counterexample_existentials)}")
    logging.debug(f"  Universal assignment: {self._format_literals(counterexample_universals)}")
    
    # Log rule fire and no_rule_fired variables grouped by existential variable
    for exist_id in self.existential_var_ids:
      exist_name = self.id_to_name.get(exist_id, f"id{exist_id}")
      logging.debug(f"  {exist_name}:")
      
      # Log no_rule_fired variables for this existential
      for eid, no_rule_fired_var_id, rule_index in self.all_no_rule_fired_vars:
        if eid == exist_id:
          no_rule_fired_name = self.id_to_name.get(no_rule_fired_var_id, f"id{no_rule_fired_var_id}")
          # Find this variable's assignment in the model
          for lit in model:
            if abs(lit) == no_rule_fired_var_id:
              value = lit > 0
              logging.debug(f"    {no_rule_fired_name} (after {rule_index} rules) = {value}")
              break
      
      # Log rule fire variables for this existential
      for eid, fire_var_id, premise_name in self.all_rule_fire_vars:
        if eid == exist_id:
          fire_var_name = self.id_to_name.get(fire_var_id, f"id{fire_var_id}")
          # Find this variable's assignment in the model
          for lit in model:
            if abs(lit) == fire_var_id:
              value = lit > 0
              logging.debug(f"    {fire_var_name} (premise: {premise_name}) = {value}")
              break
      
      # Log value variables for this existential
      for eid, value_var_id, value_index in self.all_value_vars:
        if eid == exist_id:
          value_var_name = self.id_to_name.get(abs(value_var_id), f"id{abs(value_var_id)}")
          # Find this variable's assignment in the model
          for lit in model:
            if abs(lit) == abs(value_var_id):
              value = lit > 0
              # Note: value_var_id might be negated to represent False
              if value_var_id < 0:
                value = not value
              logging.debug(f"    {value_var_name} (for rule {value_index}) = {value}")
              break

    # Step 3: Call solve again with restricted assignment and unnegated output gate
    unnegated_output = self.output_gate_id
    assumptions = counterexample_universals + counterexample_existentials + [unnegated_output]

    result2 = self.counterexample_solver.solve(assumptions=assumptions)
    
    # Assert that this call is UNSAT
    assert not result2, "Second solve call should be UNSAT but returned SAT"
    
    # Step 4: Extract failed existential assumptions
    core = self.counterexample_solver.get_core()
    core = [] if core is None else core
    existential_core = [lit for lit in core if abs(lit) in self.existential_var_ids]
    
    logging.debug(f"Counterexample verified:")
    logging.debug(f"  Existential core: {self._format_literals(existential_core)}")

    return (True, (existential_core, counterexample_universals))
  
  def analyze_counterexample(self, existential_literals: List[int], universal_literals: List[int]) -> None:
    """Analyze a counterexample to refine the model.
    
    Args:
      existential_literals: List of existential variable literals from the counterexample
      universal_literals: List of universal variable literals from the counterexample
    """
    logging.debug(f"Analyzing counterexample:")
    logging.debug(f"  Existential literals: {existential_literals}")
    logging.debug(f"  Universal literals: {universal_literals}")
    
    expansion_clause = []
    for exist_lit in existential_literals:
      exist_id = abs(exist_lit)
      exist_name = self.id_to_name.get(exist_id, exist_id)
      assignment = [lit for lit in universal_literals if abs(lit) in self.dependencies_by_id.get(exist_id, [])]
      
      logging.debug(f"  Processing {exist_name}:")
      logging.debug(f"    Universal assignment: {self._format_literals(assignment)}")
      
      expansion_var = self.get_expansion_variable(exist_id, assignment)
      
      if exist_lit > 0:
        expansion_clause.append(-expansion_var)
        self.set_default_value(exist_id, False)
        logging.debug(f"    Setting default value to False")
      else:
        expansion_clause.append(expansion_var)
        self.set_default_value(exist_id, True)
        logging.debug(f"    Setting default value to True")

    logging.debug(f"Adding expansion clause (blocking clause): {self._format_literals(expansion_clause)}")
    self.expansion_solver.add_clause(expansion_clause)
  
  def compute_model_functions(self, universal_literals: List[int]) -> Optional[List[int]]:
    """Compute the outputs of the model functions for a given universal assignment.
    
    This function determines what values the existential variables should take
    according to the current model (decision lists) given a specific assignment
    to the universal variables.
    
    Args:
      universal_literals: List of literals representing the universal assignment
      
    Returns:
      List of existential literals representing the model function outputs,
      or None if the model is unsatisfiable with this universal assignment
    """
    # Build assumptions: permanent assumptions + rule fire vars + current value vars + universal assignment
    # We add only the expansion variable assignments that are relevant to this universal assignment
    assumptions = []
    assumptions.extend(self.permanent_assumptions)
    assumptions.extend(self.rule_fire_vars.values())
    assumptions.extend(self.value_vars.values())
    assumptions.extend(universal_literals)
    
    # For each existential variable, check if there's an expansion variable for this universal assignment
    # and add its value from expansion_variable_assignment
    for exist_id in self.existential_var_ids:
      # Get the dependency set for this existential variable
      dep_set = self.dependencies_by_id.get(exist_id, set())
      
      # Extract the assignment to dependent universal variables
      assignment = [lit for lit in universal_literals if abs(lit) in dep_set]
      assignment_tuple = tuple(sorted(assignment, key=abs))
      
      # Check if we have an expansion variable for this combination
      key = (exist_id, assignment_tuple)
      if key in self.expansion_vars:
        exp_var_id = self.expansion_vars[key]
        # Find the value of this expansion variable in expansion_variable_assignment
        for lit in self.expansion_variable_assignment:
          if abs(lit) == exp_var_id:
            assumptions.append(lit)
            break
    
    logging.debug(f"Computing model functions for universal assignment: {self._format_literals(universal_literals)}")
    logging.debug(f"  Using {len(assumptions)} assumptions: {self._format_literals(assumptions)}")
    
    result = self.counterexample_solver.solve(assumptions=assumptions)
    
    if not result:
      logging.debug(f"  Model is unsatisfiable with this universal assignment")
      # Let's debug what's in the core
      core = self.counterexample_solver.get_core()
      if core:
        logging.debug(f"  Core (conflicting assumptions): {self._format_literals(core)}")
      return None
    
    # Get the model and extract existential variable assignments
    model = self.counterexample_solver.get_model()
    existential_assignment = [lit for lit in model if abs(lit) in self.existential_var_ids]
    
    logging.debug(f"  Model function outputs: {self._format_literals(existential_assignment)}")
    return existential_assignment
  
  def _enumerate_and_compute_model_functions(self) -> bool:
    """Enumerate all universal assignments and compute model function outputs for each.
    
    This is called when a satisfying model is found to show what the existential
    variables are set to for every possible universal assignment.
    
    Returns:
      True if all universal assignments have valid outputs, False otherwise
    """
    from itertools import product
    
    # Generate all possible assignments to universal variables
    num_universals = len(self.universal_var_ids)
    
    if num_universals == 0:
      # No universal variables, just compute with empty assignment
      result = self.compute_model_functions([])
      if result:
        logging.info(f"  (no universals): {self._format_literals(result)}")
        return True
      else:
        logging.error(f"  (no universals): UNSAT (no valid assignment)")
        return False
    
    all_valid = True
    # For each combination of True/False for universal variables
    for assignment_tuple in product([False, True], repeat=num_universals):
      # Convert to literals
      universal_literals = []
      for i, value in enumerate(assignment_tuple):
        var_id = self.universal_var_ids[i]
        universal_literals.append(var_id if value else -var_id)
      
      # Compute model function outputs
      result = self.compute_model_functions(universal_literals)
      
      if result:
        logging.info(f"  {self._format_literals(universal_literals)} → {self._format_literals(result)}")
      else:
        logging.error(f"  {self._format_literals(universal_literals)} → UNSAT (no valid assignment)")
        all_valid = False
    
    return all_valid
  
  def solve(self) -> bool:
    """Solve the DQBF formula.
    
    Returns:
      True if the formula is satisfiable, False otherwise
    """
    iteration = 0
    while True:
      iteration += 1
      logging.debug(f"\n=== Iteration {iteration} ===")
      
      has_counterexample, counterexample = self.get_counterexample()
      
      if not has_counterexample:
        logging.info(f"Formula is SATISFIABLE (after {iteration} iterations)")
        
        # Compute and display the model functions for all universal assignments (only in verbose mode)
        if logging.getLogger().isEnabledFor(logging.DEBUG):
          logging.info("Computing model functions for all universal assignments:")
          all_valid = self._enumerate_and_compute_model_functions()
          
          if not all_valid:
            logging.error("ERROR: Cannot compute outputs for some universal assignments")
            logging.error("This indicates an internal error in the solver")
            import sys
            sys.exit(1)
        
        return True
      
      existential_core, universal_assignment = counterexample
      
      # Check if this is the same counterexample as the last one (debugging check)
      current_exist_set = set(existential_core)
      current_univ_set = set(universal_assignment)
      
      if (self.last_counterexample_existentials is not None and 
          self.last_counterexample_universals is not None):
        if (current_exist_set == self.last_counterexample_existentials and
            current_univ_set == self.last_counterexample_universals):
          logging.error("ERROR: Same counterexample seen twice in a row!")
          logging.error(f"  Existential: {self._format_literals(existential_core)}")
          logging.error(f"  Universal: {self._format_literals(universal_assignment)}")
          logging.error("This indicates the solver is not making progress")
          import sys
          sys.exit(1)
      
      # Store this counterexample for next iteration
      self.last_counterexample_existentials = current_exist_set
      self.last_counterexample_universals = current_univ_set
      
      self.analyze_counterexample(existential_core, universal_assignment)
      
      logging.debug(f"Checking expansion solver (with {len(self.expansion_vars)} expansion variables)...")
      if not self.expansion_solver.solve():
        logging.info(f"Formula is UNSATISFIABLE (after {iteration} iterations)")
        return False
      
      model = self.expansion_solver.get_model()
      self.expansion_variable_assignment = [lit for lit in model if abs(lit) in self.expansion_vars_set]
      logging.debug(f"Expansion model found: {len(self.expansion_variable_assignment)} expansion variable assignments")
      logging.debug(f"  Assignments: {self.expansion_variable_assignment}")
  
  def detect_equivalent_existentials(self) -> Dict[int, List[int]]:
    """Detect equivalent existential variables.
    
    Two existential variables are equivalent if they have the same dependencies
    and cannot be forced to different values under any assignment to their dependencies.
    
    This method groups existentials by the number of dependencies, then for each group,
    checks pairs of variables to see if they can be different.
    
    Returns:
      Dictionary mapping a representative existential variable ID to a list of equivalent
      existential variable IDs (including the representative)
    """
    logging.info("Detecting equivalent existential variables...")

    # Union-Find data structure to track equivalence classes
    class UnionFind:
      def __init__(self, elements):
        self.parent = {elem: elem for elem in elements}
        self.rank = {elem: 0 for elem in elements}
      
      def find(self, x):
        """Find representative with path compression."""
        if self.parent[x] != x:
          self.parent[x] = self.find(self.parent[x])
        return self.parent[x]
      
      def union(self, x, y):
        """Union by rank."""
        root_x = self.find(x)
        root_y = self.find(y)
        
        if root_x == root_y:
          return
        
        # Union by rank
        if self.rank[root_x] < self.rank[root_y]:
          self.parent[root_x] = root_y
        elif self.rank[root_x] > self.rank[root_y]:
          self.parent[root_y] = root_x
        else:
          self.parent[root_y] = root_x
          self.rank[root_x] += 1
      
      def same_set(self, x, y):
        """Check if x and y are in the same equivalence class."""
        return self.find(x) == self.find(y)
      
      def get_classes(self):
        """Get all equivalence classes as a dictionary."""
        classes = {}
        for elem in self.parent:
          root = self.find(elem)
          if root not in classes:
            classes[root] = []
          classes[root].append(elem)
        return classes

    detection_solver = SAT(bootstrap_with=self.matrix)
    
    # Initialize union-find with all existential variables
    uf = UnionFind(self.existential_var_ids)
    
    # Group existentials by number of dependencies
    by_dep_count: Dict[int, List[int]] = {}
    for exist_id in self.existential_var_ids:
      dep_count = len(self.dependencies_by_id_list.get(exist_id, []))
      if dep_count not in by_dep_count:
        by_dep_count[dep_count] = []
      by_dep_count[dep_count].append(exist_id)
    
    logging.debug(f"Grouped {len(self.existential_var_ids)} existentials by dependency count:")
    for dep_count, group in sorted(by_dep_count.items()):
      logging.debug(f"  {dep_count} dependencies: {len(group)} variables")
    
    # For each group with the same dependency count
    for dep_count, group in sorted(by_dep_count.items()):
      logging.debug(f"Checking {len(group)} variables with {dep_count} dependencies...")
      
      # Check all pairs in this group
      for i in range(len(group)):
        var1_id = group[i]
        var1_name = self.id_to_name.get(var1_id, str(var1_id))
        
        for j in range(i + 1, len(group)):
          var2_id = group[j]
          var2_name = self.id_to_name.get(var2_id, str(var2_id))
          
          # Skip if already in the same equivalence class
          if uf.same_set(var1_id, var2_id):
            logging.debug(f"  Skipping {var1_name} and {var2_name}: already equivalent")
            continue
          
          # Get dependencies for both variables (in order)
          deps1 = self.dependencies_by_id_list.get(var1_id, [])
          deps2 = self.dependencies_by_id_list.get(var2_id, [])
          
          logging.debug(f"  Checking pair: {var1_name} and {var2_name}")
          logging.debug(f"    {var1_name} deps: {[self.id_to_name.get(d, str(d)) for d in deps1]}")
          logging.debug(f"    {var2_name} deps: {[self.id_to_name.get(d, str(d)) for d in deps2]}")
          
          assumption_variable = self.counter.increase()
          for dep_var1, dep_var2 in zip(deps1, deps2):
            detection_solver.add_clause([-assumption_variable, dep_var1, -dep_var2])
            detection_solver.add_clause([-assumption_variable, -dep_var1, dep_var2])

          detection_solver.add_clause([-assumption_variable, var1_id, var2_id])
          detection_solver.add_clause([-assumption_variable, -var1_id, -var2_id])

          result = detection_solver.solve(assumptions=[assumption_variable, self.output_gate_id])
          
          if not result:
            logging.info(f"  Found equivalent variables: {var1_name} and {var2_name}")
            uf.union(var1_id, var2_id)
    
    # Get final equivalence classes
    equivalence_classes = uf.get_classes()
    
    # Print summary
    logging.info(f"\nFinal equivalence classes ({len(equivalence_classes)} classes):")
    for representative, members in sorted(equivalence_classes.items()):
      if len(members) == 1:
        logging.info(f"  [{self.id_to_name.get(representative, str(representative))}]")
      else:
        member_names = [self.id_to_name.get(m, str(m)) for m in sorted(members)]
        logging.info(f"  [{', '.join(member_names)}]")
    
    return equivalence_classes
              
  
  def get_statistics(self) -> Dict[str, int]:
    """Get statistics about the formula.
    
    Returns:
      Dictionary with formula statistics
    """
    return {
      'total_variables': len(self.name_to_id),
      'universal_variables': len(self.universal_vars),
      'existential_variables': len(self.existential_vars),
      'clauses': len(self.matrix),
      'max_clause_size': max(len(clause) for clause in self.matrix) if self.matrix else 0,
      'avg_clause_size': sum(len(clause) for clause in self.matrix) / len(self.matrix) if self.matrix else 0,
      'max_dependencies': max(len(deps) for deps in self.dependencies.values()) if self.dependencies else 0,
    }
  
  def print_formula_info(self):
    """Print information about the formula."""
    stats = self.get_statistics()
    
    print("=" * 60)
    print("DQBF Formula Information")
    print("=" * 60)
    
    print(f"\nVariables:")
    print(f"  Total: {stats['total_variables']}")
    print(f"  Universal: {stats['universal_variables']}")
    print(f"  Existential: {stats['existential_variables']}")
    
    print(f"\nCNF Matrix:")
    print(f"  Clauses: {stats['clauses']}")
    print(f"  Max clause size: {stats['max_clause_size']}")
    print(f"  Avg clause size: {stats['avg_clause_size']:.2f}")
    
    print(f"\nDependencies:")
    print(f"  Max dependencies per existential var: {stats['max_dependencies']}")
    
    print(f"\nOutput gate: {self.id_to_name[self.output_gate_id]} (ID={self.output_gate_id})")
    
    print("\n" + "-" * 60)
    print("Universal Variables:")
    print("-" * 60)
    for var in self.universal_vars[:10]:
      var_id = self.name_to_id[var]
      print(f"  {var} (ID={var_id})")
    if len(self.universal_vars) > 10:
      print(f"  ... and {len(self.universal_vars) - 10} more")
    
    print("\n" + "-" * 60)
    print("Existential Variables and Dependencies:")
    print("-" * 60)
    for var in sorted(self.existential_vars):
      var_id = self.name_to_id[var]
      deps = self.dependencies[var]
      print(f"  {var} (ID={var_id}) depends on {len(deps)} variables:")
      print(f"    {', '.join(deps[:5])}{'...' if len(deps) > 5 else ''}")
    
    print("\n" + "-" * 60)
    print(f"Full CNF Encoding ({stats['clauses']} clauses):")
    print("-" * 60)
    for i, clause in enumerate(self.matrix, 1):
      # Convert clause to use variable names
      lit_strs = []
      for lit in clause:
        var_id = abs(lit)
        var_name = self.id_to_name.get(var_id, f"id{var_id}")
        if lit > 0:
          lit_strs.append(var_name)
        else:
          lit_strs.append(f"¬{var_name}")
      clause_str = ' ∨ '.join(lit_strs)
      print(f"  {i}. {clause_str}")
    
    print()
  
def main():
  """Example usage of the DQBF solver."""
  import argparse
  import os
  import sys
  import logging
  
  parser_args = argparse.ArgumentParser(
    description='DQBF Solver',
    formatter_class=argparse.RawDescriptionHelpFormatter,
    epilog="""
Example:
 python dqbf_solver.py formula.dqcir
 python dqbf_solver.py formula.dqcir -v
 python dqbf_solver.py formula.dqcir --info
    """
  )
  
  parser_args.add_argument(
    'filename',
    type=str,
    help='Path to the DQCIR file to solve'
  )
  
  parser_args.add_argument(
    '--info',
    action='store_true',
    help='Show formula information only (do not solve)'
  )
  
  parser_args.add_argument(
    '--detect-equiv',
    action='store_true',
    help='Detect equivalent existential variables (do not solve)'
  )
  
  parser_args.add_argument(
    '-v', '--verbose',
    action='store_true',
    help='Enable verbose (debug) logging'
  )
  
  args = parser_args.parse_args()
  
  # Setup logging
  log_level = logging.DEBUG if args.verbose else logging.INFO
  logging.basicConfig(
    level=log_level,
    format='%(levelname)s: %(message)s'
  )
  
  # Check if file exists
  if not os.path.isfile(args.filename):
    logging.error(f"File '{args.filename}' does not exist.")
    sys.exit(1)
  
  # Parse the DQCIR file
  logging.info(f"Parsing {args.filename}...")
  try:
    # Create parser with a fresh counter (starts at 0)
    parser = DQCIRParser(counter=Counter(0))
    
    # Parse the file
    parser.parse_file(args.filename)
    logging.debug(f"Parsed {len(parser.name_to_id)} variables and gates")
    
    # Generate CNF
    parser.tseitin_transform()
    logging.debug(f"Tseitin transformation complete: {len(parser.cnf)} clauses")
    
    # Get output gate ID
    if not parser.output_gate:
      raise ValueError("No output gate specified in the formula")
    
    output_gate_id = parser.name_to_id[parser.output_gate]
    logging.debug(f"Output gate: {parser.output_gate} (ID={output_gate_id})")
    
    # Create counter starting from max ID seen in parsing
    # This allows the solver to create new variables without conflicts
    max_id = max(parser.name_to_id.values()) if parser.name_to_id else 0
    for clause in parser.cnf:
      for lit in clause:
        max_id = max(max_id, abs(lit))
    
    logging.debug(f"Maximum variable ID: {max_id}")
    counter = Counter(max_id)
    
    # Create solver with parsed data and counter
    solver = DQBFSolver(
      name_to_id=parser.name_to_id.copy(),
      id_to_name=parser.id_to_name.copy(),
      dependencies=parser.dependencies.copy(),
      matrix=parser.cnf.copy(),
      universal_vars=parser.forall_vars_ordered.copy(),
      output_gate_id=output_gate_id,
      counter=counter
    )
    
    # Get statistics
    stats = solver.get_statistics()
    logging.debug(f"Variables: {stats['total_variables']}, Clauses: {stats['clauses']}")
    logging.debug(f"Universal variables: {stats['universal_variables']}")
    logging.debug(f"Existential variables: {stats['existential_variables']}")
    logging.debug(f"Max dependencies: {stats['max_dependencies']}")
    
  except Exception as e:
    logging.error(f"Error parsing file or creating solver: {e}")
    if args.verbose:
      import traceback
      traceback.print_exc()
    sys.exit(1)
  
  # Show detailed formula information if requested
  if args.info:
    solver.print_formula_info()
    sys.exit(0)
  
  # Detect equivalent existentials if requested
  if args.detect_equiv:
    solver.detect_equivalent_existentials()
    sys.exit(0)
  
  # Try to solve
  logging.info("Solving...")
  try:
    result = solver.solve()
    if result:
      print(f"Result: SATISFIABLE")
      sys.exit(10)
    else:
      print(f"Result: UNSATISFIABLE")
      sys.exit(20)
  except NotImplementedError:
    logging.warning("solve() method not yet implemented.")
    logging.info("This is a solver stub. Implement the solve() method to enable solving.")
    sys.exit(1)
  except KeyboardInterrupt:
    logging.warning("Solving aborted by user")
    sys.exit(1)
  except Exception as e:
    logging.error(f"Error during solving: {e}")
    if args.verbose:
      import traceback
      traceback.print_exc()
    sys.exit(1)


if __name__ == "__main__":
  main()
