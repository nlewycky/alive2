#pragma once

// Copyright (c) 2018-present The Alive2 Authors.
// Distributed under the MIT license that can be found in the LICENSE file.

#include <ostream>
#include <string>

namespace llvm {
class BasicBlock;
class Type;
class Value;
}

namespace IR {
class BasicBlock;
class Function;
class Type;
class Value;
}

namespace llvm_util {

IR::BasicBlock& getBB(const llvm::BasicBlock *bb);

std::string value_name(const llvm::Value &v);

IR::Type& get_int_type(unsigned bits);
IR::Type* llvm_type2alive(const llvm::Type *ty);

IR::Value* make_intconst(uint64_t val, int bits);
IR::Value* get_operand(llvm::Value *v);

void add_identifier(const llvm::Value &llvm, IR::Value &v);

#define PRINT(T) std::ostream& operator<<(std::ostream &os, const T &x);
PRINT(llvm::Type)
PRINT(llvm::Value)
#undef PRINT

void init_llvm_utils(std::ostream &os);
void reset_state(IR::Function &f);
}
