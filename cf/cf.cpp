#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <optional>
#include <set>
#include <tuple>
#include <utility>
#include <vector>

#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"

#include "ir/function.h"
#include "llvm_util/llvm2alive.h"
#include "llvm_util/utils.h"
#include "smt/smt.h"
#include "tools/transform.h"
#include "util/errors.h"

#include "adjacency-list.h"

// TODO: scale up during a run, just have a max.
constexpr int size = 5;

namespace {

template <typename T, T First, T Last> bool advance(std::vector<T> &ops) {
  int n = ops.size();
  int last = n - 1;
  for (int i = 0; i < n; ++i) {
    if (ops[i] < Last) {
      ++ops[i];
      return true;
    }
    assert(ops[i] == Last);
    if (i == last)
      return false;
    ops[i] = First;
  }
  return true;
}

typedef uint8_t Ops;
static const Ops FirstOp = 0;
static const Ops Add = 0;
static const Ops Sub = 1;
static const Ops Mul = 2;
static const Ops UDiv = 3;
static const Ops SDiv = 4;
static const Ops URem = 5;
static const Ops SRem = 6;
static const Ops Shl = 7;
static const Ops LShr = 8;
static const Ops AShr = 9;
static const Ops And = 10;
static const Ops Or = 11;
static const Ops Xor = 12;
static const Ops LastOp = 12;

// Out points towards arguments/inputs to the function.
unsigned out_edges(Ops op) {
  switch (op) {
  case Add:
  case Sub:
  case Mul:
  case UDiv:
  case SDiv:
  case URem:
  case SRem:
  case Shl:
  case LShr:
  case AShr:
  case And:
  case Or:
  case Xor:
    return 2;
  }
  std::abort();
}

bool commutative(Ops op) {
  switch (op) {
  case Add:
  case Mul:
  case And:
  case Or:
  case Xor:
    return true;
  default:
    return false;
  }
}

// We implement our own evaluator so we can burn through all the obvious
// non-matches quickly and without involving memory allocation before creating
// LLVM IR and sending them to alive.
int eval_op(Ops op, const std::vector<int> &v) {
  assert(v.size() == 2);
  switch (op) {
  case Add:
    return (unsigned)v[0] + (unsigned)v[1];
  case Sub:
    return (unsigned)v[0] - (unsigned)v[1];
  case Mul:
    return (unsigned)v[0] * (unsigned)v[1];
  case UDiv:
    if (v[1] == 0) return -1;
    return (unsigned)v[0] / (unsigned)v[1];
  case SDiv:
    if (v[1] == 0) return -1;
    if (v[0] == INT_MIN && v[1] == -1) return -1;
    return v[0] / v[1];
  case URem:
    if (v[1] == 0) return -1;
    return ((unsigned)v[0] % (unsigned)v[1]);
  case SRem:
    if (v[1] == 0) return -1;
    if (v[0] == INT_MIN && v[1] == -1) return -1;
    return v[0] % v[1];
  case Shl:
    return (unsigned)v[0] << (unsigned)v[1];
  case LShr:
    return (unsigned)v[0] >> (unsigned)v[1];
  case AShr:
    if ((unsigned)v[1] > sizeof(signed)) return -1;
    return v[0] >> v[1];
  case And:
    return v[0] & v[1];
  case Or:
    return v[0] | v[1];
  case Xor:
    return v[0] ^ v[1];
  }
  std::abort();
}

int eval(const SimpleRootedDigraph &g, const std::vector<Ops> &ops) {
  assert(g.size() == ops.size());
  assert(g.all_reachable());
  assert(g.is_acyclic());

  int generated_value = 3;
  auto x = g.graph();
  std::vector<std::pair<uint8_t, uint8_t>> node_stack;
  std::vector<std::optional<int>> values;
  values.resize(g.size());
  node_stack.emplace_back(0, 0);
  do {
  top:
    auto &[node, adj_i] = node_stack.back();
    assert(!values[node].has_value());
    auto &adj_list = x[node];
    for (int adj_list_length = adj_list.size(); adj_i != adj_list_length;
         ++adj_i) {
      if (!values[adj_list[adj_i]].has_value()) {
        // Stop, proceed to the child node now.
        node_stack.emplace_back(adj_list[adj_i], 0);
        goto top;
      }
    }
    std::vector<int> adj_values;
    adj_values.reserve(out_edges(ops[node]));
    for (auto adj : adj_list) {
      assert(values[adj].has_value());
      adj_values.emplace_back(values[adj].value());
    }
    while (adj_values.size() < out_edges(ops[node])) {
      adj_values.push_back(generated_value);
      ++generated_value;
    }
    values[node] = eval_op(ops[node], adj_values);
    // printf("node %d = %d\n", node, values[node].value());
    node_stack.pop_back(); // kills 'node' and 'adj_i'
  } while (!values[0]);
  return values[0].value();
}

llvm::FunctionType *build_llvm_functiontype(int free_variables_count,
                                            llvm::LLVMContext &C) {
  llvm::Type *i32 = llvm::Type::getInt32Ty(C);
  std::vector<llvm::Type*> Params;
  for (int i = 0; i != free_variables_count; ++i)
    Params.push_back(i32);
  return llvm::FunctionType::get(i32, Params, false);
}

llvm::Value *build_llvm_op(Ops o, llvm::BasicBlock *BB,
                           const std::vector<llvm::Value *> &operands) {
  switch (o) {
  case Add:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::Add,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case Sub:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::Sub,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case Mul:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::Mul,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case UDiv:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::UDiv,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case SDiv:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::SDiv,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case URem:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::URem,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case SRem:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::SRem,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case Shl:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::Shl,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case LShr:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::LShr,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case AShr:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::AShr,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case And:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::And,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case Or:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::Or,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  case Xor:
    assert(operands.size() == 2);
    return llvm::BinaryOperator::Create(llvm::Instruction::BinaryOps::Xor,
                                        operands[0], operands[1], llvm::Twine(),
                                        BB);
  }
  std::abort();
}

llvm::Function *build_llvm(const SimpleRootedDigraph &g,
                           const std::vector<Ops> &ops,
                           int free_variables, llvm::FunctionType *FTy,
                           llvm::Module *M) {
  llvm::Function *F =
    llvm::Function::Create(FTy, llvm::GlobalValue::ExternalLinkage, "", M);
  llvm::BasicBlock *BB = llvm::BasicBlock::Create(FTy->getContext(), "", F);

  auto x = g.graph();
  std::vector<std::pair<uint8_t, uint8_t>> node_stack;
  std::vector<std::optional<llvm::Value *>> values;
  values.resize(g.size());
  node_stack.emplace_back(0, 0);
  llvm::Function::arg_iterator AI = F->arg_begin();
  do {
  top:
    auto &[node, adj_i] = node_stack.back();
    assert(!values[node].has_value());
    auto &adj_list = x[node];
    for (int adj_list_length = adj_list.size(); adj_i != adj_list_length;
         ++adj_i) {
      if (!values[adj_list[adj_i]].has_value()) {
        // Stop, proceed to the child node now.
        node_stack.emplace_back(adj_list[adj_i], 0);
        goto top;
      }
    }
    std::vector<llvm::Value *> adj_values;
    adj_values.reserve(out_edges(ops[node]));
    for (auto adj : adj_list) {
      assert(values[adj].has_value());
      adj_values.emplace_back(values[adj].value());
    }
    while (adj_values.size() < out_edges(ops[node])) {
      adj_values.push_back(AI);
      ++AI;
    }
    values[node] = build_llvm_op(ops[node], BB, adj_values);
    node_stack.pop_back(); // kills 'node' and 'adj_i'
  } while (!values[0]);

  llvm::ReturnInst::Create(FTy->getContext(), values[0].value(), BB);

  return F;
}

bool skip_commutative(const SimpleRootedDigraph &g,
                      const std::vector<Ops> &ops) {
  // If a node has a commutative op assigned, check that its adjacencies are in
  // ascending order. If not, we can skip this one.
  auto adjacency_list = g.graph();
  for (int i = 0, e = adjacency_list.size(); i != e; ++i) {
    if (!commutative(ops[i]))
      continue;
    auto node = adjacency_list[i];
    auto [min, max] = g.out_degree_spec(i);
    assert(max > 0);
    // Never skip 'add %other_node, %arg' or anything with an arg in it. Args
    // are always ordered.
    if (g.out_degree(i) < max)
      continue;
    int last_out_node = node[0];
    for (int j = 1; j != max; ++j) {
      if (node[j] < last_out_node)
        return true;
      last_out_node = node[j];
    }
  }
  return false;
}

}

int main(void) {
  llvm::LLVMContext Context;
  llvm::Module M("", Context);
  llvm::TargetLibraryInfoImpl TLI_impl;
  llvm::TargetLibraryInfo TLI(TLI_impl);

  llvm_util::initializer llvm_util_init(std::cerr, M.getDataLayout());
  smt::smt_initializer smt_init;

  // We want to efficiently generate every possible DAG of expressions on the
  // operators we want to fold.
  //
  // To make this tractable, we order the search in a specific way:
  // - The actual graph contains only the operations, none of the variables.
  //   Variables have no out-edges and are never shared. If you want to know
  //   whether op(x, x) folds, use op(x, y) /\ x == y.
  // - We can exploit the fact that our nodes have an out-degree known in
  //   advance. The `add` instruction takes two arguments, never one or three.
  //   There's no need to try to create a node with three out-edges when none of
  //   our operations have three out-edges.
  // - That's why it's more efficient to use an adjacency list representation.
  //   Each node has a single row with a maximum number of out-edges (the
  //   "out-degree-spec") to other nodes.
  // - A nodes out edges are ordered, as not all operations are commutable. The
  //   adjacency list entries 'node 1: [2, 3]' and 'node 1: [3, 2]' are
  //   distinct.
  // - We grow the graph by trying to add one edge at a time, starting from then
  //   empty graph.
  //   * Once a graph has a cycle, adding more edges can never break the cycle.
  //     If the graph has a path a -> b, then we don't try adding edge b -> a.
  //   * We want our graph to use all its nodes. Not using all the nodes implies
  //     that it's equivalent to a smaller graph that we would have explored
  //     in a previous iteration.
  // - We have a hash function over the graphs and use it to avoid duplicates.
  // - Once a graph is created, we try out every possible assignment over the
  //   nodes, based on what is valid for the out-degree of the node. Recall
  //   that we don't include variables as nodes in our graph, so an 'add' which
  //   requires an out-degree of 2, fits a node with out-degree of 0, 1, or 2.
  // - We now have a graph with an assignment of operators to nodes.

  std::vector<std::tuple<uint8_t, uint8_t>> out_degree;
  for (int i = 0; i < size; ++i)
    out_degree.emplace_back(UINT8_C(2), UINT8_C(2));

  // Create all 1-edge graphs, where the edge is root-to-each other node.
  // Skip hashing and cycle checking checking since they're unique by
  // construction and skip reachability testing.
  std::vector<SimpleRootedDigraph> v;

  // This holds all the graphs. The hash function must be high quality so as to
  // uniquely identify each graph.
  std::map<uint64_t, SimpleRootedDigraph> hashes;

  if (size == 1) {
    v.emplace_back(SimpleRootedDigraph(out_degree));
  } else {
    v.reserve(size - 1);
    for (int i = 1; i < size; ++i) {
      v.emplace_back(SimpleRootedDigraph(out_degree));
      v.back().add_edge(0, i);
    }
    if (size == 2) {
      assert(v.size() == 1);
      hashes.insert({SimpleRootedDigraphHash{}(v.back()), v.back()});
    }
  }

  if (size > 2) {
    do {
#ifndef NDEBUG
      std::map<uint64_t, SimpleRootedDigraph> v2_hashes;
#else
      std::set<uint64_t> v2_hashes;
#endif
      std::vector<SimpleRootedDigraph> v2;
      for (const auto &g : v) {
        for (int i = 0; i < size; ++i) {
          auto [min_out_degree, max_out_degree] = g.out_degree_spec(i);
          int out_degree = g.out_degree(i);
          if (out_degree == max_out_degree)
            continue;
          for (int j = 1; j < size; ++j) {
            if (i == j)
              continue;
            if (g.edge(i, j))
              continue;
            if (i == 0 || !g.has_path(j, i)) {
              SimpleRootedDigraph g2(g);
              g2.add_edge(i, j);
              assert(g2.is_acyclic());
              auto hash = SimpleRootedDigraphHash{}(g2);
#ifndef NDEBUG
              auto [it, did_insert] = v2_hashes.insert({hash, g2});
              if (!did_insert) {
                if (it->second != g2) {
                  printf("Same hash=%lx but inequal graphs:\n", hash);
                  it->second.dump();
                  v2.back().dump();
                  std::abort();
                }
              }
#else
              auto [_, did_insert] = v2_hashes.insert(hash);
#endif
              if (did_insert) {
                v2.push_back(g2);
                if (g2.all_reachable()) {
                  auto [it, did_insert] = hashes.insert({hash, g2});
                  (void)it;
#ifndef NDEBUG
                  if (!did_insert) {
                    if (it->second != g2) {
                      printf("Same hash=%lx but inequal graphs:\n", hash);
                      it->second.dump();
                      v2.back().dump();
                      std::abort();
                    }
                  }
#endif
                }
              }
            }
          }
        }
      }
      std::swap(v, v2);
    } while (!v.empty());
  }

  std::vector<Ops> ops;
  for (int i = 0; i < size; ++i)
    ops.push_back(Add);

  // After assigning operators we can determine how many free variables there
  // are on the expression. We group our expressions based on how many free
  // variables they have. They can't be equal to each other unless one of them
  // isn't using all its variables, which we scan for explicitly.

  // buckets[free_variable_count][eval_result][:]<0=graph, 1=ops>
  constexpr unsigned bucket_max = 0x7ff;
  std::vector<std::vector<
      std::vector<std::tuple<SimpleRootedDigraph, std::vector<Ops>>>>>
      buckets(
          size * size,
          std::vector<
              std::vector<std::tuple<SimpleRootedDigraph, std::vector<Ops>>>>(
              bucket_max + 1)); // TODO: this wastes a little memory.

  for (const auto &[_, graph] : hashes) {
    std::vector<Ops> ops(size, FirstOp);
    int free_variable_count = 0;
    for (int i = 0; i < size; ++i) {
      free_variable_count +=
          std::get<0>(graph.out_degree_spec(i)) - graph.out_degree(i);
    }
    do {
      // TODO: we could skip faster by advancing op[n] instead of just skipping
      //       one at a time.
      // TODO: we could skip faster by skipping to next known non-commutative
      //       op instead of just trying the next op.
      if (skip_commutative(graph, ops))
        continue;
      unsigned bucket = (unsigned)eval(graph, ops) & bucket_max;
      assert(bucket <= bucket_max);
      buckets[free_variable_count][bucket].emplace_back(graph, ops);
    } while (advance<Ops, FirstOp, LastOp>(ops));
  }

  for (int free_variable_count = 0, fe = buckets.size();
       free_variable_count != fe; ++free_variable_count) {
    if (buckets[free_variable_count].empty())
      continue;
    for (int i = 0; i != bucket_max; ++i) {
      if (buckets[free_variable_count][i].size() == 0)
        continue;
      auto FTy = build_llvm_functiontype(free_variable_count, Context);
      std::vector<IR::Function> Fns;
      Fns.reserve(buckets[free_variable_count][i].size());
      for (const auto &[graph, ops] : buckets[free_variable_count][i]) {
        auto llvm_fn = build_llvm(graph, ops, free_variable_count, FTy, &M);
        auto alive_fn = llvm_util::llvm2alive(*llvm_fn, TLI);
        assert(alive_fn.has_value());
        Fns.emplace_back(std::move(alive_fn.value()));
      }
      int equivalent = 0, different = 0;
      for (unsigned f = 0; f < Fns.size(); ++f) {
        unsigned g = (f + 1 != Fns.size()) ? (f + 1) : 0;
        tools::Transform t;
        // !!!!!!!
        t.src = std::move(Fns[f]);
        t.tgt = std::move(Fns[g]);
        // TODO: this is probably a no-op? unsure.
        // t.preprocess();
        // TODO: what does "check_each_var = true/false" do?
        tools::TransformVerify verifier(t, false);
        assert(verifier.getTypings());
        if (util::Errors errs = verifier.verify()) {
          ++different;
        } else {
          ++equivalent;
        }
        Fns[f] = std::move(t.src);
        Fns[g] = std::move(t.tgt);
      }
      printf("== %u, != %u\n", equivalent, different);
      // TODO: if necessary, form new equivalence classes.
      // Ordinarily we expect two normal cases:
      // 1. a small number of functions, all equivalent.
      //    Check f0 <= f1 <= f2 <= f0 and we're done.
      // 2. a large number of functions, many equivalence classes, lots of
      //    which are 1-element.
    }
  }

  // TODO: ...
  // Given a graph with an assignment of operators to nodes, we can check
  // whether there are 'magic' constants for some of the variables which cause
  // the output to be constant.
  // - Graphs with different number of free variables are never equal, so we
  //   divide them up that way first.

  // TODO: ...
  // Given a graph with an assignment of operators to nodes, we can check
  // whether there are 'magic' constants for some of the variables which cause
  // the output to be one of the other variables.
}