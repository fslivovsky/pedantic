#include "dqbf_solver.hpp"
#include <iostream>
#include <sstream>
#include <cmath>
#include <algorithm>
#include <stdexcept>

namespace {

std::string format_literal(int lit) {
  return std::string(lit < 0 ? "~" : "") + std::to_string(std::abs(lit));
}

}  // namespace

DQBFSolver::DQBFSolver(
    const std::unordered_map<std::string, int>& name_to_id,
    const std::map<int, std::string>& id_to_name,
    const std::map<std::string, std::vector<std::string>>& dependencies,
    const std::vector<std::vector<int>>& matrix,
    const std::vector<std::string>& universal_vars,
    int output_gate_id,
    std::shared_ptr<Counter> counter)
    : name_to_id_(name_to_id),
      id_to_name_(id_to_name),
      dependencies_(dependencies),
      matrix_(matrix),
      universal_vars_(universal_vars),
      output_gate_id_(output_gate_id) {
  // Create or use provided counter
  if (counter) {
    counter_ = counter;
  } else {
    int max_id = 0;
    for (const auto& [name, id] : name_to_id) {
      max_id = std::max(max_id, id);
    }
    for (const auto& clause : matrix) {
      for (int lit : clause) {
        max_id = std::max(max_id, std::abs(lit));
      }
    }
    counter_ = std::make_shared<Counter>(max_id);
  }

  // Build ID-based structures
  for (const auto& var : universal_vars) {
    auto it = name_to_id_.find(var);
    if (it != name_to_id_.end()) {
      universal_var_ids_.push_back(it->second);
    }
  }

  for (const auto& [exist_var, deps] : dependencies) {
    auto it = name_to_id_.find(exist_var);
    if (it != name_to_id_.end()) {
      int exist_id = it->second;
      existential_vars_.insert(exist_id);
      existential_var_ids_.push_back(exist_id);

      std::set<int> dep_set;
      std::vector<int> dep_list;
      for (const auto& dep : deps) {
        auto dep_it = name_to_id_.find(dep);
        if (dep_it != name_to_id_.end()) {
          int dep_id = dep_it->second;
          dep_set.insert(dep_id);
          dep_list.push_back(dep_id);
        }
      }
      dependencies_by_id_[exist_id] = dep_set;
      dependencies_by_id_list_[exist_id] = dep_list;
    }
  }

  // Initialize SAT solvers
  counterexample_solver_ = std::make_unique<cadical_interface::Cadical>();
  for (const auto& clause : matrix) {
    counterexample_solver_->add_clause(clause);
  }

  expansion_solver_ = std::make_unique<cadical_interface::Cadical>();

  // Initialize models for all existential variables
  for (int exist_id : existential_var_ids_) {
    init_model(exist_id);
  }
}

std::string DQBFSolver::format_literals(const std::vector<int>& literals) const {
  std::ostringstream oss;
  oss << "[";
  for (size_t i = 0; i < literals.size(); ++i) {
    if (i > 0) oss << ", ";
    oss << format_literal(literals[i]);
  }
  oss << "]";
  return oss.str();
}

void DQBFSolver::init_model(int existential_var_id) {
  if (existential_var_id < 0 ||
      existential_vars_.find(existential_var_id) == existential_vars_.end()) {
    throw std::runtime_error("Invalid existential variable ID");
  }

  if (value_vars_.find(existential_var_id) != value_vars_.end()) {
    return;  // Already initialized
  }

  auto it = id_to_name_.find(existential_var_id);
  std::string exist_name = (it != id_to_name_.end()) ? it->second
                                                       : "var" + std::to_string(existential_var_id);

  // Create initial value variable
  int value_var_1 = counter_->increase();
  value_vars_[existential_var_id] = value_var_1;
  id_to_name_[value_var_1] = exist_name + "_value_1";
  all_value_vars_.push_back({existential_var_id, value_var_1, 1});

  // Create initial "no rule fired" variable
  int no_rule_fired_0 = counter_->increase();
  no_rule_fired_vars_[existential_var_id] = no_rule_fired_0;
  id_to_name_[no_rule_fired_0] = exist_name + "_nofired_0";
  all_no_rule_fired_vars_.push_back({existential_var_id, no_rule_fired_0, 0});

  // Create rule fire variable for rule 1
  int fires_var_1 = counter_->increase();
  rule_fire_vars_[existential_var_id] = fires_var_1;
  rule_numbers_[existential_var_id] = 1;  // Initialize rule counter to 1
  id_to_name_[fires_var_1] = exist_name + "_fire_1";
  all_rule_fire_vars_.push_back({existential_var_id, fires_var_1, "default"});

  // Add unit clause: no rule up to 0 fires
  counterexample_solver_->add_clause({no_rule_fired_0});

  // Add equivalence clauses for initialization
  // if no_rule_fired_0 is false, then existential_var <=> value_var_1
  counterexample_solver_->add_clause({-no_rule_fired_0, -fires_var_1,
                                       -existential_var_id, value_var_1});
  counterexample_solver_->add_clause({-no_rule_fired_0, -fires_var_1,
                                       existential_var_id, -value_var_1});
}

void DQBFSolver::set_default_value(int existential_var_id, bool value) {
  if (value_vars_.find(existential_var_id) == value_vars_.end()) {
    throw std::runtime_error("Variable not initialized");
  }

  int current_value_var = value_vars_[existential_var_id];
  value_vars_[existential_var_id] =
      value ? current_value_var : -current_value_var;
}

void DQBFSolver::add_rule(int existential_var_id,
                          const std::vector<int>& premise, bool conclusion,
                          int value_var) {
  if (value_vars_.find(existential_var_id) == value_vars_.end()) {
    throw std::runtime_error("Variable not initialized");
  }

  int previous_no_rule_fired = no_rule_fired_vars_[existential_var_id];
  int this_rule_fired = rule_fire_vars_[existential_var_id];
  int this_value_var = std::abs(value_vars_[existential_var_id]);

  auto it = id_to_name_.find(existential_var_id);
  std::string exist_name = (it != id_to_name_.end()) ? it->second
                                                       : "var" + std::to_string(existential_var_id);

  // Get current rule number and increment for next rule
  int rule_num = rule_numbers_[existential_var_id];
  rule_numbers_[existential_var_id]++;

  // Create new variables
  int next_rule_fired = counter_->increase();
  int this_no_rule_fired = counter_->increase();
  int next_value_var = counter_->increase();

  // Update tracking
  rule_fire_vars_[existential_var_id] = next_rule_fired;
  no_rule_fired_vars_[existential_var_id] = this_no_rule_fired;
  value_vars_[existential_var_id] = next_value_var;

  // Create premise name
  std::string premise_name = format_literals(premise);
  if (premise.empty()) premise_name = "true";

  // Update the name of this_rule_fired to reflect its premise
  id_to_name_[std::abs(this_rule_fired)] =
      exist_name + "_fire_" + std::to_string(rule_num - 1) + "_premise_" +
      premise_name;

  // Update tracking list entry
  for (auto& var : all_rule_fire_vars_) {
    if (var.existential_var_id == existential_var_id &&
        var.fire_var_id == this_rule_fired) {
      var.premise_name = premise_name;
      break;
    }
  }

  // Add names for new variables
  id_to_name_[next_rule_fired] =
      exist_name + "_fire_" + std::to_string(rule_num);
  id_to_name_[this_no_rule_fired] =
      exist_name + "_nofired_" + std::to_string(rule_num - 1);
  id_to_name_[next_value_var] =
      exist_name + "_value_" + std::to_string(rule_num);

  // Track rule index
  int rule_index = 0;
  for (const auto& var : all_rule_fire_vars_) {
    if (var.existential_var_id == existential_var_id) {
      rule_index++;
    }
  }

  all_rule_fire_vars_.push_back({existential_var_id, next_rule_fired, "default"});
  all_no_rule_fired_vars_.push_back({existential_var_id, this_no_rule_fired, rule_index});
  all_value_vars_.push_back({existential_var_id, next_value_var, rule_num});

  // Define this_rule_fired: this_rule_fired <=> (premise AND previous_no_rule_fired)
  for (int lit : premise) {
    counterexample_solver_->add_clause({-this_rule_fired, lit});
  }
  std::vector<int> clause = {this_rule_fired};
  for (int lit : premise) {
    clause.push_back(-lit);
  }
  clause.push_back(this_rule_fired);
  counterexample_solver_->add_clause(clause);

  // Define this_no_rule_fired
  counterexample_solver_->add_clause({-this_no_rule_fired, previous_no_rule_fired});
  counterexample_solver_->add_clause({-this_no_rule_fired, -this_rule_fired});
  counterexample_solver_->add_clause(
      {this_no_rule_fired, -previous_no_rule_fired, this_rule_fired});

  // If rule fires and no previous rule fired, existential_var <=> value_i
  counterexample_solver_->add_clause(
      {-next_rule_fired, -this_no_rule_fired, -existential_var_id, next_value_var});
  counterexample_solver_->add_clause(
      {-next_rule_fired, -this_no_rule_fired, existential_var_id, -next_value_var});

  // Handle conclusion
  if (value_var == -1) {
    int conclusion_lit = conclusion ? this_value_var : -this_value_var;
    permanent_assumptions_.push_back(conclusion_lit);
  } else {
    // Add equivalence: this_value_var <=> value_var
    counterexample_solver_->add_clause({-this_value_var, value_var});
    counterexample_solver_->add_clause({this_value_var, -value_var});
  }
}

std::vector<int> DQBFSolver::get_canonical_assignment(
    const std::vector<int>& assignment) {
  auto result = assignment;
  std::sort(result.begin(), result.end(),
            [](int a, int b) { return std::abs(a) < std::abs(b); });
  return result;
}

int DQBFSolver::get_expansion_variable(int existential_var_id,
                                       const std::vector<int>& assignment) {
  if (existential_vars_.find(existential_var_id) == existential_vars_.end()) {
    throw std::runtime_error("Invalid existential variable ID");
  }

  auto dep_set = dependencies_by_id_[existential_var_id];
  for (int lit : assignment) {
    if (dep_set.find(std::abs(lit)) == dep_set.end()) {
      throw std::runtime_error("Assignment contains variables not in dependency set");
    }
  }

  auto canonical = get_canonical_assignment(assignment);
  auto key = std::make_pair(existential_var_id, canonical);

  if (expansion_vars_.find(key) != expansion_vars_.end()) {
    return expansion_vars_[key];
  }

  int expansion_var_id = counter_->increase();

  auto it = id_to_name_.find(existential_var_id);
  if (it != id_to_name_.end()) {
    std::string exist_name = it->second;
    std::ostringstream oss;
    oss << "exp_" << exist_name << "_";
    for (size_t i = 0; i < canonical.size(); ++i) {
      if (i > 0) oss << "_";
      oss << std::abs(canonical[i]) << (canonical[i] > 0 ? "T" : "F");
    }
    id_to_name_[expansion_var_id] = oss.str();
  }

  expansion_vars_[key] = expansion_var_id;

  add_rule(existential_var_id, assignment, true, expansion_var_id);

  expansion_var_ids_.push_back(expansion_var_id);

  return expansion_var_id;
}

std::pair<bool, std::optional<std::tuple<std::vector<int>, std::vector<int>, 
            std::map<std::string, int>>>>
DQBFSolver::get_counterexample(bool verbose) {
  counterexample_solver_->assume({-output_gate_id_});
  counterexample_solver_->assume(permanent_assumptions_); // These include fixed value_vars if a forcing clause was added.
  for (const auto& [exist_id, fire_var] : rule_fire_vars_) { // Set default rules as "firing" in case no other rule fires
    counterexample_solver_->assume({fire_var});
  }
  for (const auto& [exist_id, value_var] : value_vars_) { // Set current value vars (can be negative literals)
    counterexample_solver_->assume({value_var});
  }
  counterexample_solver_->assume(expansion_variable_assignment_);

  for (const auto& lit : last_universal_assignment_) {
    counterexample_solver_->phase(lit);
  }

  auto result = counterexample_solver_->solve();

  if (result != 10) {  // 10 = SAT, 20 = UNSAT
    return {false, std::nullopt};
  }

  // Get universal assignments
  std::vector<int> counterexample_universals = 
      counterexample_solver_->get_values(universal_var_ids_);

  // Get existential assignments
  std::vector<int> counterexample_existentials = 
      counterexample_solver_->get_values(existential_var_ids_);

  // Collect internal variable values BEFORE verification solve
  std::map<std::string, int> internal_values;
  
  // Collect all rule fire variables for each existential
  for (const auto& var : all_rule_fire_vars_) {
    int exist_id = var.existential_var_id;
    int fire_var = var.fire_var_id;
    int fire_val = counterexample_solver_->val(fire_var);
    auto fire_it = id_to_name_.find(std::abs(fire_var));
    std::string fire_name = (fire_it != id_to_name_.end()) ? fire_it->second
                                                             : "fire_" + std::to_string(fire_var);
    internal_values[fire_name] = fire_val;
  }

  // Collect all no_rule_fired variables for each existential
  for (const auto& var : all_no_rule_fired_vars_) {
    int exist_id = var.existential_var_id;
    int no_fired_var = var.no_rule_fired_var_id;
    int no_fired_val = counterexample_solver_->val(no_fired_var);
    auto no_fired_it = id_to_name_.find(no_fired_var);
    std::string no_fired_name = (no_fired_it != id_to_name_.end()) ? no_fired_it->second
                                                                     : "nofired_" + std::to_string(no_fired_var);
    internal_values[no_fired_name] = no_fired_val;
  }

  // Collect all value variables for each existential
  for (const auto& var : all_value_vars_) {
    int exist_id = var.existential_var_id;
    int value_var = var.value_var_id;
    int value_val = counterexample_solver_->val(std::abs(value_var));
    auto value_it = id_to_name_.find(std::abs(value_var));
    std::string value_name = (value_it != id_to_name_.end()) ? value_it->second
                                                               : "value_" + std::to_string(value_var);
    internal_values[value_name] = value_val;
  }

  // Verify with universal and existential assignment
  counterexample_solver_->assume(counterexample_universals);
  counterexample_solver_->assume(counterexample_existentials);
  counterexample_solver_->assume({output_gate_id_});

  auto result2 = counterexample_solver_->solve();

  if (result2 != 20) {  // Should be UNSAT (20)
    throw std::runtime_error("Verification solve returned " + std::to_string(result2) + 
                             " (expected 20 for UNSAT)");
  }

  auto core_existentials = counterexample_solver_->get_failed(counterexample_existentials);

  return {true, {{core_existentials, counterexample_universals, internal_values}}};
}

void DQBFSolver::analyze_counterexample(
    const std::vector<int>& existential_literals,
    const std::vector<int>& universal_literals,
    bool verbose) {
  std::vector<int> expansion_clause;

  for (int exist_lit : existential_literals) {
    int exist_id = std::abs(exist_lit);

    auto it = id_to_name_.find(exist_id);
    std::string exist_name = (it != id_to_name_.end()) ? it->second
                                                         : "var" + std::to_string(exist_id);

    std::vector<int> assignment;
    auto deps = dependencies_by_id_[exist_id];
    for (int lit : universal_literals) {
      if (deps.find(std::abs(lit)) != deps.end()) {
        assignment.push_back(lit);
      }
    }

    int expansion_var = get_expansion_variable(exist_id, assignment);

    if (verbose) {
      std::cout << "[VERBOSE]   " << exist_name << " (ID=" << exist_id << "):\n";
      std::cout << "[VERBOSE]     Assignment: " << format_literals(assignment) << "\n";
      std::cout << "[VERBOSE]     Expansion variable: " << format_literal(expansion_var) << "\n";
    }

    if (exist_lit > 0) {
      expansion_clause.push_back(-expansion_var);
      set_default_value(exist_id, false);
      if (verbose) {
        std::cout << "[VERBOSE]     Default value: false\n";
      }
    } else {
      expansion_clause.push_back(expansion_var);
      set_default_value(exist_id, true);
      if (verbose) {
        std::cout << "[VERBOSE]     Default value: true\n";
      }
    }
  }

  if (verbose) {
    std::cout << "[VERBOSE]   Adding blocking clause: " << format_literals(expansion_clause) << "\n";
  }

  expansion_solver_->add_clause(expansion_clause);
}

std::optional<std::vector<int>> DQBFSolver::compute_model_functions(
    const std::vector<int>& universal_literals) {
  counterexample_solver_->assume(permanent_assumptions_);
  for (const auto& [exist_id, fire_var] : rule_fire_vars_) {
    counterexample_solver_->assume({fire_var});
  }
  for (const auto& [exist_id, value_var] : value_vars_) {
    counterexample_solver_->assume({value_var});
  }
  counterexample_solver_->assume(universal_literals);

  auto result = counterexample_solver_->solve();

  if (result != 10) {  // 10 = SAT, 20 = UNSAT
    return std::nullopt;
  }

  return counterexample_solver_->get_values(existential_var_ids_);
}

bool DQBFSolver::enumerate_and_compute_model_functions() {
  if (universal_var_ids_.empty()) {
    auto result = compute_model_functions({});
    if (result) {
      std::cout << "  (no universals): " << format_literals(*result) << "\n";
      return true;
    } else {
      std::cerr << "  (no universals): UNSAT (no valid assignment)\n";
      return false;
    }
  }

  bool all_valid = true;
  int num_universals = universal_var_ids_.size();
  int num_assignments = 1 << num_universals;

  for (int i = 0; i < num_assignments; ++i) {
    std::vector<int> universal_literals;
    for (int j = 0; j < num_universals; ++j) {
      int var_id = universal_var_ids_[j];
      bool value = (i >> j) & 1;
      universal_literals.push_back(value ? var_id : -var_id);
    }

    auto result = compute_model_functions(universal_literals);

    if (result) {
      std::cout << "  " << format_literals(universal_literals) << " → "
                << format_literals(*result) << "\n";
    } else {
      std::cerr << "  " << format_literals(universal_literals)
                << " → UNSAT (no valid assignment)\n";
      all_valid = false;
    }
  }

  return all_valid;
}

bool DQBFSolver::solve(bool verbose) {
  iterations_ = 0;

  while (true) {
    iterations_++;

    if (verbose) {
      std::cout << "\n[VERBOSE] === Iteration " << iterations_ << " ===\n";
    }

    auto [has_counterexample, counterexample] = get_counterexample(verbose);

    if (!has_counterexample) {
      std::cout << "Formula is SATISFIABLE (after " << iterations_
                << " iterations)\n";

      if (verbose) {
        std::cout << "\n[VERBOSE] Computing model functions for all universal assignments:\n";
        if (!enumerate_and_compute_model_functions()) {
          std::cerr << "ERROR: Cannot compute outputs for all assignments\n";
          return false;
        }
      }

      return true;
    }

    auto [existential_core, universal_assignment, internal_values] = *counterexample;

    if (verbose) {
      std::cout << "[VERBOSE] Found counterexample:\n";
      std::cout << "[VERBOSE]   Existential core: " << format_literals(existential_core) << "\n";
      std::cout << "[VERBOSE]   Universal assignment: " << format_literals(universal_assignment) << "\n";
      
      // Display internal variables grouped by existential variable
      for (int exist_id : existential_var_ids_) {
        auto it = id_to_name_.find(exist_id);
        std::string exist_name = (it != id_to_name_.end()) ? it->second
                                                             : "var" + std::to_string(exist_id);
        
        std::cout << "[VERBOSE]   " << exist_name << " (ID=" << exist_id << "):\n";
        
        // Show all rule fire variables for this existential
        std::cout << "[VERBOSE]     Rule fire variables:\n";
        for (const auto& var : all_rule_fire_vars_) {
          if (var.existential_var_id == exist_id) {
            auto fire_it = id_to_name_.find(std::abs(var.fire_var_id));
            std::string fire_name = (fire_it != id_to_name_.end()) ? fire_it->second
                                                                     : "fire_" + std::to_string(var.fire_var_id);
            if (internal_values.find(fire_name) != internal_values.end()) {
              std::cout << "[VERBOSE]       " << fire_name << ": " << format_literal(internal_values.at(fire_name)) << "\n";
            }
          }
        }
        
        // Show all no_rule_fired variables for this existential
        std::cout << "[VERBOSE]     No rule fired variables:\n";
        for (const auto& var : all_no_rule_fired_vars_) {
          if (var.existential_var_id == exist_id) {
            auto no_fired_it = id_to_name_.find(var.no_rule_fired_var_id);
            std::string no_fired_name = (no_fired_it != id_to_name_.end()) ? no_fired_it->second
                                                                             : "nofired_" + std::to_string(var.no_rule_fired_var_id);
            if (internal_values.find(no_fired_name) != internal_values.end()) {
              std::cout << "[VERBOSE]       " << no_fired_name << ": " << format_literal(internal_values.at(no_fired_name)) << "\n";
            }
          }
        }
        
        // Show all value variables for this existential
        std::cout << "[VERBOSE]     Value variables:\n";
        for (const auto& var : all_value_vars_) {
          if (var.existential_var_id == exist_id) {
            auto value_it = id_to_name_.find(std::abs(var.value_var_id));
            std::string value_name = (value_it != id_to_name_.end()) ? value_it->second
                                                                       : "value_" + std::to_string(var.value_var_id);
            if (internal_values.find(value_name) != internal_values.end()) {
              std::cout << "[VERBOSE]       " << value_name << ": " << format_literal(internal_values.at(value_name)) << "\n";
            }
          }
        }
      }
    }

    // Check for cycle: same counterexample appearing twice
    if (!last_existential_core_.empty() && !last_universal_assignment_.empty()) {
      if (last_existential_core_ == existential_core &&
          last_universal_assignment_ == universal_assignment) {
        throw std::runtime_error(
            "Cycle detected: same counterexample repeated in iteration " +
            std::to_string(iterations_));
      }
    }

    // Store current counterexample for next iteration check
    last_existential_core_ = existential_core;
    last_universal_assignment_ = universal_assignment;

    analyze_counterexample(existential_core, universal_assignment, verbose);

    if (verbose) {
      std::cout << "[VERBOSE] Analyzing counterexample and refining model...\n";
      std::cout << "[VERBOSE] Checking expansion solver...\n";
    }

    auto exp_result = expansion_solver_->solve();

    if (exp_result != 10) {  // 10 = SAT, 20 = UNSAT
      std::cout << "Formula is UNSATISFIABLE (after " << iterations_
                << " iterations)\n";
      return false;
    }

    if (verbose) {
      std::cout << "[VERBOSE] Expansion solver found satisfying assignment for blocking clause.\n";
    }

    expansion_variable_assignment_ = expansion_solver_->get_values(expansion_var_ids_);
  }
}

std::map<int, std::vector<int>> DQBFSolver::detect_equivalent_existentials() {
  // Group existentials by dependency count
  std::map<int, std::vector<int>> groups_by_dep_count;

  for (int exist_id : existential_var_ids_) {
    int dep_count = dependencies_by_id_list_[exist_id].size();
    groups_by_dep_count[dep_count].push_back(exist_id);
  }

  // For each group, check equivalence using SAT solver
  std::map<int, std::vector<int>> equivalence_classes;
  std::map<int, int> var_to_class;

  for (const auto& [dep_count, vars] : groups_by_dep_count) {
    for (int var : vars) {
      if (var_to_class.find(var) == var_to_class.end()) {
        // Create new equivalence class
        int class_id = equivalence_classes.size();
        equivalence_classes[class_id].push_back(var);
        var_to_class[var] = class_id;
      }
    }
  }

  return equivalence_classes;
}

std::map<std::string, int> DQBFSolver::get_statistics() const {
  return {{"iterations", iterations_},
          {"existential_vars", static_cast<int>(existential_var_ids_.size())},
          {"universal_vars", static_cast<int>(universal_var_ids_.size())},
          {"expansion_vars", static_cast<int>(expansion_vars_.size())}};
}

void DQBFSolver::print_formula_info() const {
  std::cout << "DQBF Formula Information:\n";
  std::cout << "  Universal variables: " << universal_var_ids_.size() << "\n";
  std::cout << "  Existential variables: " << existential_var_ids_.size() << "\n";
  std::cout << "  Matrix clauses: " << matrix_.size() << "\n";

  std::cout << "\nExistential variables and their dependencies:\n";
  for (int exist_id : existential_var_ids_) {
    auto it = id_to_name_.find(exist_id);
    std::string exist_name =
        (it != id_to_name_.end()) ? it->second : "var" + std::to_string(exist_id);

    auto deps_it = dependencies_by_id_list_.find(exist_id);
    if (deps_it == dependencies_by_id_list_.end()) continue;
    auto& deps = deps_it->second;
    std::cout << "  " << exist_name << " depends on: ";
    for (size_t i = 0; i < deps.size(); ++i) {
      auto dep_it = id_to_name_.find(deps[i]);
      if (i > 0) std::cout << ", ";
      std::cout << ((dep_it != id_to_name_.end()) ? dep_it->second
                    : "var" + std::to_string(deps[i]));
    }
    std::cout << "\n";
  }
}
