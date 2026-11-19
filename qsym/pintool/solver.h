#ifndef QSYM_SOLVER_H_
#define QSYM_SOLVER_H_

#include <z3++.h>
#include <fstream>
#include <unordered_map>
#include <unordered_set>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>

#include "pin.H"

#include "afl_trace_map.h"
#include "expr.h"
// #include "thread_context.h"
#include "expr_builder.h"
#include "dependency.h"

namespace qsym {

extern z3::context *g_z3_context;
typedef std::unordered_set<ExprRef, ExprRefHash, ExprRefEqual> ExprRefSetTy;

class Solver {
public:
  ExprRefSetTy updated_exprs_;
  ExprRefSetTy added_exprs_;

  Solver(
      const std::string input_file,
      const std::string out_dir,
      const std::string bitmap);
  virtual ~Solver() = default;

  void push();
  void reset();
  void pop();
  void add(z3::expr expr);
  z3::check_result check();

  bool checkAndSave(const std::string& postfix="");
  void addJcc(ExprRef, bool, ADDRINT);
  void addAddr(ExprRef, ADDRINT);
  void addAddr(ExprRef, llvm::APInt);
  void addValue(ExprRef, ADDRINT);
  void addValue(ExprRef, llvm::APInt);
  void solveAll(ExprRef, llvm::APInt);
  UINT8 getInput(ADDRINT index);

  ADDRINT last_pc() { return last_pc_; }

  // a new translation block starts at guest address pc
  void noteBlock(ADDRINT pc);

  // a conditional jump at `at` will go to `jump` or `fall`
  void noteJcc(ADDRINT at, ADDRINT jump, ADDRINT fall);

  // a call, or a return, identified by the call's return address (the address
  // after the call instruction, where the matching return goes)
  void noteCall(ADDRINT ret_addr);
  void noteRet(ADDRINT ret_addr);

protected:
  std::string input_file_;
  std::vector<UINT8> inputs_;
  std::string out_dir_;
  z3::context& context_;
  z3::solver solver_;
  std::string session_;
  INT32 num_generated_;
  AflTraceMap trace_;
  bool last_interested_;
  bool syncing_;
  uint64_t start_time_;
  uint64_t solving_time_;
  ADDRINT last_pc_;
  DependencyForest<Expr> dep_forest_;

  // frontier export
  FILE* frontier_fp_ = nullptr;
  bool frontier_only_ = false;
  bool frontier_all_ = false;
  uint64_t frontier_seq_ = 0;

  ADDRINT               current_block_ = 0;
  struct PendingBranch {
    ADDRINT pc;
    bool taken;
    bool interesting;
    unsigned n;
    std::string asserts; // ids of its #ASSERT records, in order (a-b = a..b)
    uint64_t id; // which symbolic constraint of the trace this is (constraints_)
  };
  std::vector<PendingBranch> frontier_pending_;

  std::unordered_map<unsigned, uint32_t> assert_ids_;
  std::vector<z3::expr> assert_pinned_;
  std::string exportAsserts();

  bool blocks_on_ = false;
  ADDRINT blocks_lo_ = 0, blocks_hi_ = 0;
  std::unordered_set<ADDRINT> blocks_seen_;

  bool calls_on_ = false;
  std::string calls_deferred_; // #CALL/#RET records waiting for their block's branch records
  void exportCall(const char* kind, ADDRINT ret_addr);

  uint64_t constraints_ = 0;
  struct {
    ADDRINT at, jump, fall;
    uint64_t after;
    bool valid;
  } jcc_ = {0, 0, 0, 0, false};

  void exportBranch(ExprRef e, bool taken, ADDRINT pc, bool is_interesting);
  void flushFrontier(ADDRINT pc);

  void checkOutDir();
  void readInput();

  std::vector<UINT8> getConcreteValues();
  virtual void saveValues(const std::string& postfix);
  void printValues(const std::vector<UINT8>& values);

  z3::expr getPossibleValue(z3::expr& z3_expr);
  z3::expr getMinValue(z3::expr& z3_expr);
  z3::expr getMaxValue(z3::expr& z3_expr);

  void addToSolver(ExprRef e, bool taken);
  void syncConstraints(ExprRef e);

  void addConstraint(ExprRef e, bool taken, bool is_interesting);
  void addConstraint(ExprRef e);
  bool addRangeConstraint(ExprRef, bool);
  void addNormalConstraint(ExprRef, bool);

  ExprRef getRangeConstraint(ExprRef e, bool is_unsigned);

  bool isInterestingJcc(ExprRef, bool, ADDRINT);
  void negatePath(ExprRef, bool);
  void solveOne(z3::expr);

  void checkFeasible();
};

extern Solver* g_solver;

} // namespace qsym

#endif // QSYM_SOLVER_H_
