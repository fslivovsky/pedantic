#ifndef DQBF_SOLVER_HPP
#define DQBF_SOLVER_HPP

#include <string>
#include <unordered_map>
#include <map>
#include <set>
#include <vector>
#include <memory>
#include <optional>
#include <tuple>
#include "counter.hpp"
#include "cadical_solver.hpp"

/**
 * Tracks a rule fire variable with its premise
 */
struct RuleFireVar {
  int existential_var_id;
  int fire_var_id;
  std::string premise_name;
};

/**
 * Tracks a "no rule fired" variable with its index
 */
struct NoRuleFiredVar {
  int existential_var_id;
  int no_rule_fired_var_id;
  int rule_index;
};

/**
 * Tracks a value variable with its index
 */
struct ValueVar {
  int existential_var_id;
  int value_var_id;
  int rule_index;
};

/**
 * DQBF Solver using CEGAR (Counter-Example Guided Abstraction Refinement)
 * with ordered decision lists
 */
class DQBFSolver {
 public:
  /**
   * Initialize the DQBF solver
   * @param name_to_id Mapping from variable names to IDs
   * @param id_to_name Mapping from IDs to variable names
   * @param dependencies Map from existential var name to list of universal var names
   * @param matrix CNF clauses (each clause is a vector of integers)
   * @param universal_vars List of universal variable names in order
   * @param output_gate_id ID of the output gate
   * @param counter Optional Counter for ID generation
   */
  DQBFSolver(
      const std::unordered_map<std::string, int>& name_to_id,
      const std::map<int, std::string>& id_to_name,
      const std::map<std::string, std::vector<std::string>>& dependencies,
      const std::vector<std::vector<int>>& matrix,
      const std::vector<std::string>& universal_vars,
      int output_gate_id,
      std::shared_ptr<Counter> counter = nullptr);

  /**
   * Initialize the model for an existential variable
   * @param existential_var_id ID of the existential variable
   */
  void init_model(int existential_var_id);

  /**
   * Set the default value for an existential variable's decision list
   * @param existential_var_id ID of the existential variable
   * @param value The default value (true or false)
   */
  void set_default_value(int existential_var_id, bool value);

  /**
   * Add a rule to the decision list for an existential variable
   * @param existential_var_id ID of the existential variable
   * @param premise List of literals forming the rule's premise
   * @param conclusion The value to assign if the rule fires
   * @param value_var Optional variable ID for the conclusion
   */
  void add_rule(int existential_var_id, const std::vector<int>& premise,
                bool conclusion, int value_var = -1);

  /**
   * Get or create an expansion variable
   * @param existential_var_id ID of the existential variable
   * @param assignment List of literals for the universal assignment
   * @return The expansion variable ID
   */
  int get_expansion_variable(int existential_var_id,
                             const std::vector<int>& assignment);

  /**
   * Get a counterexample
   * @return (has_counterexample, (existential_core, universal_assignment))
   */
  /**
   * Get a counterexample
   * @param verbose Whether to print verbose output
   * @return (has_counterexample, (existential_core, universal_assignment, internal_values))
   *         where internal_values is a map of variable names to their assignments for verbose output
   */
  std::pair<bool, std::optional<std::tuple<std::vector<int>, std::vector<int>, 
            std::map<std::string, int>>>>
  get_counterexample(bool verbose = false);

  /**
   * Analyze a counterexample and refine the model
   * @param existential_literals Existential variable literals from counterexample
   * @param universal_literals Universal variable literals from counterexample
   * @param verbose Whether to print verbose output
   */
  void analyze_counterexample(const std::vector<int>& existential_literals,
                              const std::vector<int>& universal_literals,
                              bool verbose = false);

  /**
   * Compute model function outputs for a given universal assignment
   * @param universal_literals List of universal variable literals
   * @return Optional list of existential variable outputs
   */
  std::optional<std::vector<int>> compute_model_functions(
      const std::vector<int>& universal_literals);

  /**
   * Solve the DQBF formula
   * @param verbose Whether to print verbose output
   * @return True if satisfiable, false if unsatisfiable
   */
  bool solve(bool verbose = false);

  /**
   * Detect equivalent existential variables
   * @return Map from equivalence class to list of variable IDs
   */
  std::map<int, std::vector<int>> detect_equivalent_existentials();

  /**
   * Get statistics about the solving process
   */
  std::map<std::string, int> get_statistics() const;

  /**
   * Print formula information
   */
  void print_formula_info() const;

 private:
  // Core data
  std::unordered_map<std::string, int> name_to_id_;
  std::map<int, std::string> id_to_name_;
  std::map<std::string, std::vector<std::string>> dependencies_;
  std::vector<std::vector<int>> matrix_;
  std::vector<std::string> universal_vars_;
  int output_gate_id_;
  std::shared_ptr<Counter> counter_;

  // Variable tracking
  std::set<int> existential_vars_;
  std::vector<int> universal_var_ids_;
  std::vector<int> existential_var_ids_;
  std::map<int, std::set<int>> dependencies_by_id_;
  std::map<int, std::vector<int>> dependencies_by_id_list_;

  // Decision list structures
  std::map<int, int> value_vars_;
  std::map<int, int> no_rule_fired_vars_;
  std::map<int, int> rule_fire_vars_;
  std::map<int, int> rule_numbers_;  // Track current rule number for each existential

  std::vector<RuleFireVar> all_rule_fire_vars_;
  std::vector<NoRuleFiredVar> all_no_rule_fired_vars_;
  std::vector<ValueVar> all_value_vars_;

  std::vector<int> permanent_assumptions_;

  // Expansion structures
  std::map<std::pair<int, std::vector<int>>, int> expansion_vars_;
  std::vector<int> expansion_var_ids_;  // All expansion variable IDs in order
  std::vector<int> expansion_variable_assignment_;

  // SAT solvers
  std::unique_ptr<cadical_interface::Cadical> counterexample_solver_;
  std::unique_ptr<cadical_interface::Cadical> expansion_solver_;

  // Statistics
  int iterations_ = 0;

  // Cycle detection
  std::vector<int> last_existential_core_;
  std::vector<int> last_universal_assignment_;

  // Helper methods
  std::string format_literals(const std::vector<int>& literals) const;
  std::vector<int> get_canonical_assignment(const std::vector<int>& assignment);
  bool enumerate_and_compute_model_functions();
};

#endif  // DQBF_SOLVER_HPP
