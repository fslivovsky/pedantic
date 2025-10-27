#ifndef DQCIR_PARSER_HPP
#define DQCIR_PARSER_HPP

#include <string>
#include <unordered_map>
#include <map>
#include <set>
#include <vector>
#include <memory>
#include "counter.hpp"

/**
 * Gate information stored in the parser
 */
struct Gate {
  std::string type;  // "and", "or", or "xor"
  std::vector<std::pair<int, bool>> inputs;  // (variable_id, is_negated)
};

/**
 * Parser for DQBF formulas in DQCIR format
 *
 * DQCIR format:
 * - forall(...) blocks introduce universal variables
 * - exists(...) blocks introduce existential variables
 * - depend(...) specifies dependencies for existential variables
 * - gate_name = and/or/xor(...) defines logic gates
 * - output(...) specifies the output gate
 */
class DQCIRParser {
 public:
  /**
   * Initialize the parser
   * @param counter Optional Counter for ID generation. If nullptr, creates a new one.
   */
  explicit DQCIRParser(std::shared_ptr<Counter> counter = nullptr);

  /**
   * Parse a DQCIR file
   * @param filename Path to the file to parse
   */
  void parse_file(const std::string& filename);

  /**
   * Parse from a string
   * @param content The DQCIR content as a string
   */
  void parse_string(const std::string& content);

  /**
   * Get the mapping from variable names to IDs
   */
  const std::unordered_map<std::string, int>& get_name_to_id() const {
    return name_to_id_;
  }

  /**
   * Get the mapping from IDs to variable names
   */
  const std::map<int, std::string>& get_id_to_name() const {
    return id_to_name_;
  }

  /**
   * Get all universal variable names
   */
  const std::set<std::string>& get_forall_vars() const {
    return forall_vars_;
  }

  /**
   * Get all existential variable names
   */
  const std::set<std::string>& get_exists_vars() const {
    return exists_vars_;
  }

  /**
   * Get universal variables in order of introduction
   */
  const std::vector<std::string>& get_forall_vars_ordered() const {
    return forall_vars_ordered_;
  }

  /**
   * Get dependencies for an existential variable
   * @param var_name The existential variable name
   * @return List of universal variable names it depends on, or empty list if not found
   */
  std::vector<std::string> get_dependencies(const std::string& var_name) const;

  /**
   * Get dependencies by variable ID
   * @param var_id The existential variable ID
   * @return List of universal variable IDs it depends on, or empty list if not found
   */
  std::vector<int> get_dependencies_by_id(int var_id) const;

  /**
   * Get gate information
   * @param gate_id The gate ID
   * @return Gate structure or nullptr if not found
   */
  const Gate* get_gate_info(int gate_id) const;

  /**
   * Get the output gate ID
   */
  int get_output_gate_id() const { return output_gate_id_; }

  /**
   * Apply Tseitin transformation to convert gates to CNF
   * @return Vector of clauses (each clause is a vector of integers)
   */
  std::vector<std::vector<int>> tseitin_transform();

  /**
   * Get the generated CNF
   */
  const std::vector<std::vector<int>>& get_cnf() const {
    return cnf_;
  }

  /**
   * Print a summary of the parsed formula
   * @param show_cnf Whether to show sample CNF clauses
   */
  void print_summary(bool show_cnf = false) const;

  /**
   * Get the counter object
   */
  std::shared_ptr<Counter> get_counter() const {
    return counter_;
  }

  /**
   * Get the count of auxiliary variables created during Tseitin transformation
   */
  int get_aux_var_count() const {
    return aux_vars_.size();
  }

 private:
  std::shared_ptr<Counter> counter_;
  std::unordered_map<std::string, int> name_to_id_;
  std::map<int, std::string> id_to_name_;

  std::set<std::string> forall_vars_;
  std::set<std::string> exists_vars_;
  std::vector<std::string> forall_vars_ordered_;

  std::map<std::string, std::vector<std::string>> dependencies_;
  std::map<int, Gate> gates_;

  int output_gate_id_;
  std::vector<std::vector<int>> cnf_;
  std::set<int> aux_vars_;

  // Helper methods
  int get_or_create_id(const std::string& name);
  std::pair<int, bool> parse_literal(const std::string& literal);
  void parse_line(const std::string& line);
  void parse_forall(const std::string& line);
  void parse_exists(const std::string& line);
  void parse_depend(const std::string& line);
  void parse_output(const std::string& line);
  void parse_gate(const std::string& line);

  int create_aux_var(const std::string& name_hint = "");
  void tseitin_and(int gate_id, const std::vector<std::pair<int, bool>>& inputs);
  void tseitin_or(int gate_id, const std::vector<std::pair<int, bool>>& inputs);
  void tseitin_xor(int gate_id, const std::vector<std::pair<int, bool>>& inputs);
  void tseitin_xor2(int out_id, int lit1, int lit2);
};

#endif  // DQCIR_PARSER_HPP
