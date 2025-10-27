/**
 * Main program for C++ DQBF Solver
 * 
 * Usage:
 *   ./dqbf_solver <dqcir_file> [options]
 *   
 * Options:
 *   --info              Show formula information only
 *   --detect-equiv      Detect equivalent existential variables
 *   -v, --verbose       Enable detailed logging during solving
 *   -h, --help          Show help message
 */

#include "dqcir_parser.hpp"
#include "dqbf_solver.hpp"
#include <iostream>
#include <fstream>
#include <chrono>
#include <CLI/CLI.hpp>

int main(int argc, char* argv[]) {
  CLI::App app{"C++ DQBF Solver - Solves Dependency Quantified Boolean Formulas"};

  std::string filename;
  bool show_info = false;
  bool detect_equiv = false;
  bool verbose = false;

  app.add_option("file", filename, "Path to DQCIR file to solve")
      ->required()
      ->check(CLI::ExistingFile);

  app.add_flag("--info", show_info, "Show formula information only");
  app.add_flag("--detect-equiv", detect_equiv, "Detect equivalent existential variables");
  app.add_flag("-v,--verbose", verbose, "Enable detailed logging during solving");

  CLI11_PARSE(app, argc, argv);

  try {
    // Parse the DQCIR file
    std::cout << "Parsing " << filename << "...\n";
    DQCIRParser parser;
    parser.parse_file(filename);

    // Show summary if verbose or info mode requested
    if (verbose || show_info) {
      parser.print_summary(false);
    }

    // Show information if requested
    if (show_info) {
      return 0;
    }

    // Get parsed data
    auto name_to_id = parser.get_name_to_id();
    auto id_to_name = parser.get_id_to_name();
    auto universal_vars = parser.get_forall_vars_ordered();
    int output_gate_id = parser.get_output_gate_id();

    // Build dependencies map from parser
    std::map<std::string, std::vector<std::string>> dependencies_map;
    for (const auto& exist_var : parser.get_exists_vars()) {
      dependencies_map[exist_var] = parser.get_dependencies(exist_var);
    }

    // Transform to CNF
    std::cout << "\nApplying Tseitin transformation...\n";
    auto cnf = parser.tseitin_transform();
    std::cout << "Generated " << cnf.size() << " CNF clauses.\n";

    if (verbose) {
      std::cout << "\n[VERBOSE] CNF Matrix:\n";
      for (size_t i = 0; i < std::min(size_t(10), cnf.size()); ++i) {
        std::cout << "  [" << i << "] ";
        for (int lit : cnf[i]) {
          std::cout << (lit > 0 ? "" : "-") << std::abs(lit) << " ";
        }
        std::cout << "0\n";
      }
      if (cnf.size() > 10) {
        std::cout << "  ... and " << (cnf.size() - 10) << " more clauses\n";
      }
    }

    // Create solver
    std::cout << "\nCreating solver...\n";
    DQBFSolver solver(name_to_id, id_to_name, dependencies_map, cnf,
                      universal_vars, output_gate_id, parser.get_counter());

    if (verbose) {
      std::cout << "\n[VERBOSE] Solver initialized with:\n";
      std::cout << "  - " << universal_vars.size() << " universal variables\n";
      std::cout << "  - " << parser.get_exists_vars().size() << " existential variables\n";
      std::cout << "  - Output gate ID: " << output_gate_id << "\n";
    }

    // Detect equivalence if requested
    if (detect_equiv) {
      std::cout << "\nDetecting equivalent existential variables...\n";
      auto equiv_classes = solver.detect_equivalent_existentials();
      std::cout << "Found " << equiv_classes.size() << " equivalence classes:\n";
      for (const auto& [class_id, vars] : equiv_classes) {
        std::cout << "  Class " << class_id << ": ";
        for (size_t i = 0; i < vars.size(); ++i) {
          if (i > 0) std::cout << ", ";
          auto it = id_to_name.find(vars[i]);
          std::cout << ((it != id_to_name.end()) ? it->second
                        : "var" + std::to_string(vars[i]));
        }
        std::cout << "\n";
      }
      return 0;
    }

    // Solve
    std::cout << "\nSolving...\n";
    auto start = std::chrono::high_resolution_clock::now();

    bool result = solver.solve(verbose);

    auto end = std::chrono::high_resolution_clock::now();
    auto duration =
        std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

    std::cout << "\nResult: " << (result ? "SATISFIABLE" : "UNSATISFIABLE")
              << "\n";
    std::cout << "Time: " << duration.count() << " ms\n";

    auto stats = solver.get_statistics();
    std::cout << "Statistics:\n";
    for (const auto& [key, value] : stats) {
      std::cout << "  " << key << ": " << value << "\n";
    }

    return result ? 10 : 20;

  } catch (const std::exception& e) {
    std::cerr << "ERROR: " << e.what() << "\n";
    return 1;
  }
}
