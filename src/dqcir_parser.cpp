#include "dqcir_parser.hpp"
#include <fstream>
#include <sstream>
#include <algorithm>
#include <cctype>
#include <iostream>
#include <stdexcept>

namespace {

std::vector<std::string> split(const std::string& str, char delimiter) {
  std::vector<std::string> tokens;
  std::string token;
  std::istringstream stream(str);
  while (std::getline(stream, token, delimiter)) {
    tokens.push_back(token);
  }
  return tokens;
}

std::string trim(const std::string& str) {
  auto start = str.begin();
  while (start != str.end() && std::isspace(*start)) {
    ++start;
  }
  auto end = str.end();
  do {
    --end;
  } while (std::distance(start, end) > 0 && std::isspace(*end));
  return std::string(start, end + 1);
}

}  // namespace

DQCIRParser::DQCIRParser(std::shared_ptr<Counter> counter)
    : counter_(counter ? counter : std::make_shared<Counter>(0)),
      output_gate_id_(-1) {}

void DQCIRParser::parse_file(const std::string& filename) {
  std::ifstream file(filename);
  if (!file.is_open()) {
    throw std::runtime_error("Cannot open file: " + filename);
  }

  std::string line;
  while (std::getline(file, line)) {
    line = trim(line);
    if (line.empty() || line[0] == '#') {
      continue;
    }
    parse_line(line);
  }
}

void DQCIRParser::parse_string(const std::string& content) {
  std::istringstream stream(content);
  std::string line;
  while (std::getline(stream, line)) {
    line = trim(line);
    if (line.empty() || line[0] == '#') {
      continue;
    }
    parse_line(line);
  }
}

int DQCIRParser::get_or_create_id(const std::string& name) {
  auto it = name_to_id_.find(name);
  if (it != name_to_id_.end()) {
    return it->second;
  }
  int new_id = counter_->increase();
  name_to_id_[name] = new_id;
  id_to_name_[new_id] = name;
  return new_id;
}

std::pair<int, bool> DQCIRParser::parse_literal(const std::string& literal) {
  std::string lit = trim(literal);
  if (lit[0] == '-') {
    return {get_or_create_id(lit.substr(1)), true};
  }
  return {get_or_create_id(lit), false};
}

std::vector<std::string> DQCIRParser::get_dependencies(
    const std::string& var_name) const {
  auto it = dependencies_.find(var_name);
  if (it != dependencies_.end()) {
    return it->second;
  }
  return {};
}

std::vector<int> DQCIRParser::get_dependencies_by_id(int var_id) const {
  auto it = id_to_name_.find(var_id);
  if (it == id_to_name_.end()) {
    return {};
  }
  auto var_name = it->second;
  auto deps = get_dependencies(var_name);
  std::vector<int> dep_ids;
  for (const auto& dep : deps) {
    auto dep_it = name_to_id_.find(dep);
    if (dep_it != name_to_id_.end()) {
      dep_ids.push_back(dep_it->second);
    }
  }
  return dep_ids;
}

const Gate* DQCIRParser::get_gate_info(int gate_id) const {
  auto it = gates_.find(gate_id);
  if (it != gates_.end()) {
    return &it->second;
  }
  return nullptr;
}

void DQCIRParser::parse_line(const std::string& line) {
  if (line.find("forall(") == 0) {
    parse_forall(line);
  } else if (line.find("exists(") == 0) {
    parse_exists(line);
  } else if (line.find("depend(") == 0) {
    parse_depend(line);
  } else if (line.find("output(") == 0) {
    parse_output(line);
  } else if (line.find('=') != std::string::npos) {
    parse_gate(line);
  }
}

void DQCIRParser::parse_forall(const std::string& line) {
  size_t start = line.find('(') + 1;
  size_t end = line.rfind(')');
  std::string vars_str = line.substr(start, end - start);

  auto vars = split(vars_str, ',');
  for (const auto& var : vars) {
    std::string v = trim(var);
    if (!v.empty()) {
      get_or_create_id(v);
      forall_vars_.insert(v);
      forall_vars_ordered_.push_back(v);
    }
  }
}

void DQCIRParser::parse_exists(const std::string& line) {
  size_t start = line.find('(') + 1;
  size_t end = line.rfind(')');
  std::string vars_str = line.substr(start, end - start);

  auto vars = split(vars_str, ',');
  for (const auto& var : vars) {
    std::string v = trim(var);
    if (!v.empty()) {
      get_or_create_id(v);
      exists_vars_.insert(v);
      dependencies_[v] = forall_vars_ordered_;
    }
  }
}

void DQCIRParser::parse_depend(const std::string& line) {
  size_t start = line.find('(') + 1;
  size_t end = line.rfind(')');
  std::string content = line.substr(start, end - start);

  auto parts = split(content, ',');
  if (parts.empty()) {
    return;
  }

  std::string exist_var = trim(parts[0]);
  get_or_create_id(exist_var);
  exists_vars_.insert(exist_var);

  std::vector<std::string> deps;
  for (size_t i = 1; i < parts.size(); ++i) {
    std::string dep = trim(parts[i]);
    if (!dep.empty()) {
      deps.push_back(dep);
      get_or_create_id(dep);
    }
  }
  dependencies_[exist_var] = deps;
}

void DQCIRParser::parse_output(const std::string& line) {
  size_t start = line.find('(') + 1;
  size_t end = line.rfind(')');
  std::string gate_name = trim(line.substr(start, end - start));
  output_gate_id_ = get_or_create_id(gate_name);
}

void DQCIRParser::parse_gate(const std::string& line) {
  size_t eq_pos = line.find('=');
  if (eq_pos == std::string::npos) {
    return;
  }

  std::string gate_name = trim(line.substr(0, eq_pos));
  std::string gate_def = trim(line.substr(eq_pos + 1));

  std::string gate_type;
  if (gate_def.find("and(") == 0 || gate_def.find("AND(") == 0) {
    gate_type = "and";
  } else if (gate_def.find("or(") == 0 || gate_def.find("OR(") == 0) {
    gate_type = "or";
  } else if (gate_def.find("xor(") == 0 || gate_def.find("XOR(") == 0) {
    gate_type = "xor";
  } else {
    return;
  }

  size_t start = gate_def.find('(') + 1;
  size_t end = gate_def.rfind(')');
  std::string inputs_str = gate_def.substr(start, end - start);

  std::vector<std::pair<int, bool>> inputs;
  auto input_parts = split(inputs_str, ',');
  for (const auto& inp : input_parts) {
    std::string i = trim(inp);
    if (!i.empty()) {
      auto [inp_id, is_negated] = parse_literal(i);
      inputs.push_back({inp_id, is_negated});
    }
  }

  int gate_id = get_or_create_id(gate_name);
  gates_[gate_id] = Gate{gate_type, inputs};
}

int DQCIRParser::create_aux_var(const std::string& name_hint) {
  int aux_id = counter_->increase();
  std::string aux_name = "_aux_" + name_hint + "_" + std::to_string(aux_id);
  id_to_name_[aux_id] = aux_name;
  name_to_id_[aux_name] = aux_id;
  aux_vars_.insert(aux_id);
  return aux_id;
}

std::vector<std::vector<int>> DQCIRParser::tseitin_transform() {
  cnf_.clear();

  for (const auto& [gate_id, gate_info] : gates_) {
    if (gate_info.type == "and") {
      tseitin_and(gate_id, gate_info.inputs);
    } else if (gate_info.type == "or") {
      tseitin_or(gate_id, gate_info.inputs);
    } else if (gate_info.type == "xor") {
      tseitin_xor(gate_id, gate_info.inputs);
    }
  }

  return cnf_;
}

void DQCIRParser::tseitin_and(int gate_id,
                              const std::vector<std::pair<int, bool>>& inputs) {
  // gate_id => each input: -gate_id OR input
  for (auto [inp_id, is_negated] : inputs) {
    int literal = is_negated ? -inp_id : inp_id;
    cnf_.push_back({-gate_id, literal});
  }

  // all inputs => gate_id: gate_id OR -input1 OR -input2 OR ...
  std::vector<int> clause = {gate_id};
  for (auto [inp_id, is_negated] : inputs) {
    int literal = is_negated ? inp_id : -inp_id;
    clause.push_back(literal);
  }
  cnf_.push_back(clause);
}

void DQCIRParser::tseitin_or(int gate_id,
                             const std::vector<std::pair<int, bool>>& inputs) {
  // each input => gate_id: -literal OR gate_id
  for (auto [inp_id, is_negated] : inputs) {
    int literal = is_negated ? -inp_id : inp_id;
    cnf_.push_back({-literal, gate_id});
  }

  // gate_id => at least one input: -gate_id OR input1 OR input2 OR ...
  std::vector<int> clause = {-gate_id};
  for (auto [inp_id, is_negated] : inputs) {
    int literal = is_negated ? -inp_id : inp_id;
    clause.push_back(literal);
  }
  cnf_.push_back(clause);
}

void DQCIRParser::tseitin_xor(int gate_id,
                              const std::vector<std::pair<int, bool>>& inputs) {
  if (inputs.empty()) {
    cnf_.push_back({-gate_id});
    return;
  }

  if (inputs.size() == 1) {
    auto [inp_id, is_negated] = inputs[0];
    if (is_negated) {
      cnf_.push_back({-gate_id, -inp_id});
      cnf_.push_back({gate_id, inp_id});
    } else {
      cnf_.push_back({-gate_id, inp_id});
      cnf_.push_back({gate_id, -inp_id});
    }
    return;
  }

  if (inputs.size() == 2) {
    auto [inp1_id, is_neg1] = inputs[0];
    auto [inp2_id, is_neg2] = inputs[1];
    int lit1 = is_neg1 ? -inp1_id : inp1_id;
    int lit2 = is_neg2 ? -inp2_id : inp2_id;
    tseitin_xor2(gate_id, lit1, lit2);
    return;
  }

  // More than 2 inputs: chain XORs through auxiliary variables
  auto [inp1_id, is_neg1] = inputs[0];
  auto [inp2_id, is_neg2] = inputs[1];
  int lit1 = is_neg1 ? -inp1_id : inp1_id;
  int lit2 = is_neg2 ? -inp2_id : inp2_id;

  int aux_id = create_aux_var(std::string("xor_") + std::to_string(gate_id));
  tseitin_xor2(aux_id, lit1, lit2);

  int prev_aux = aux_id;
  for (size_t i = 2; i < inputs.size() - 1; ++i) {
    auto [inp_id, is_negated] = inputs[i];
    int lit = is_negated ? -inp_id : inp_id;

    int new_aux =
        create_aux_var(std::string("xor_") + std::to_string(gate_id) + "_" +
                       std::to_string(i));
    tseitin_xor2(new_aux, prev_aux, lit);
    prev_aux = new_aux;
  }

  auto [last_inp_id, last_is_neg] = inputs.back();
  int last_lit = last_is_neg ? -last_inp_id : last_inp_id;
  tseitin_xor2(gate_id, prev_aux, last_lit);
}

void DQCIRParser::tseitin_xor2(int out_id, int lit1, int lit2) {
  cnf_.push_back({-out_id, -lit1, -lit2});
  cnf_.push_back({-out_id, lit1, lit2});
  cnf_.push_back({out_id, -lit1, lit2});
  cnf_.push_back({out_id, lit1, -lit2});
}

void DQCIRParser::print_summary(bool show_cnf) const {
  std::cout << "============================================================\n";
  std::cout << "DQCIR Parser Summary\n";
  std::cout << "============================================================\n";
  std::cout << "\nTotal variables/gates: " << counter_->value() << "\n";
  std::cout << "Universal variables: " << forall_vars_.size() << "\n";
  std::cout << "Existential variables: " << exists_vars_.size() << "\n";
  std::cout << "Gates: " << gates_.size() << "\n";

  if (output_gate_id_ >= 0) {
    auto it = id_to_name_.find(output_gate_id_);
    if (it != id_to_name_.end()) {
      std::cout << "Output gate: " << it->second << "\n";
    }
  }

  if (!aux_vars_.empty()) {
    std::cout << "Auxiliary variables (Tseitin): " << aux_vars_.size() << "\n";
  }

  if (!cnf_.empty()) {
    std::cout << "CNF clauses: " << cnf_.size() << "\n";
  }

  std::cout << "\n" << std::string(60, '-') << "\n";
  std::cout << "Existential Variables and Dependencies:\n";
  std::cout << std::string(60, '-') << "\n";
  for (const auto& [var, deps] : dependencies_) {
    auto it = name_to_id_.find(var);
    if (it != name_to_id_.end()) {
      std::cout << "  " << var << " (ID=" << it->second << ") depends on: ";
      for (size_t i = 0; i < deps.size(); ++i) {
        std::cout << deps[i];
        if (i < deps.size() - 1) std::cout << ", ";
      }
      std::cout << "\n";
    }
  }

  std::cout << "\n" << std::string(60, '-') << "\n";
  std::cout << "Sample Gates (first 10):\n";
  std::cout << std::string(60, '-') << "\n";
  int count = 0;
  for (const auto& [gate_id, gate_info] : gates_) {
    if (count >= 10) break;
    auto it = id_to_name_.find(gate_id);
    if (it != id_to_name_.end()) {
      std::cout << "  " << it->second << " (ID=" << gate_id << ") = "
                << gate_info.type << "(";
      for (size_t i = 0; i < gate_info.inputs.size(); ++i) {
        if (gate_info.inputs[i].second) std::cout << "-";
        auto inp_it = id_to_name_.find(gate_info.inputs[i].first);
        if (inp_it != id_to_name_.end()) {
          std::cout << inp_it->second;
        } else {
          std::cout << gate_info.inputs[i].first;
        }
        if (i < gate_info.inputs.size() - 1) std::cout << ", ";
      }
      std::cout << ")\n";
    }
    count++;
  }

  if (gates_.size() > 10) {
    std::cout << "  ... and " << (gates_.size() - 10) << " more gates\n";
  }

  if (show_cnf && !cnf_.empty()) {
    std::cout << "\n" << std::string(60, '-') << "\n";
    std::cout << "CNF Clauses (first 10):\n";
    std::cout << std::string(60, '-') << "\n";
    for (size_t i = 0; i < std::min(size_t(10), cnf_.size()); ++i) {
      std::cout << "  Clause " << (i + 1) << ": (";
      for (size_t j = 0; j < cnf_[i].size(); ++j) {
        std::cout << cnf_[i][j];
        if (j < cnf_[i].size() - 1) std::cout << " v ";
      }
      std::cout << ")\n";
    }
    if (cnf_.size() > 10) {
      std::cout << "  ... and " << (cnf_.size() - 10) << " more clauses\n";
    }
  }
}
