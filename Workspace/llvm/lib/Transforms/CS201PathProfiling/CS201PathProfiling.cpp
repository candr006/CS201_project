/*
 * Authors: Name(s) <email(s)>
 * 
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/ADT/iterator.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/IR/CFG.h"
#include <stack>
#include <set>
#include <iostream>
#include <string>

using namespace llvm;

namespace {

  static Function* printf_prototype(LLVMContext& ctx, Module *mod) {
    std::vector<Type*> printf_arg_types;
    printf_arg_types.push_back(Type::getInt8PtrTy(ctx));
 
    FunctionType* printf_type = FunctionType::get(Type::getInt32Ty(ctx), printf_arg_types, true);
    Function *func = mod->getFunction("printf");
    if(!func)
      func = Function::Create(printf_type, Function::ExternalLinkage, Twine("printf"), mod);
    func->setCallingConv(CallingConv::C);
    return func;
  }

  struct CS201PathProfiling : public DominatorTreeWrapperPass {
  static char ID;
  //CS201PathProfiling() : FunctionPass(ID) {}
	LLVMContext *Context;

    GlobalVariable *bbCounter = NULL;
    GlobalVariable *BasicBlockPrintfFormatStr = NULL;
    Function *printf_func = NULL;

    std::vector<std::set<BasicBlock *> > loop_vector;
    std::vector<bool> is_innermost;
 
    //----------------------------------
    bool doInitialization(Module &M) {
      errs() << "\n---------Starting BasicBlockDemo---------\n";
      Context = &M.getContext();
      bbCounter = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::InternalLinkage, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0), "bbCounter");
      const char *finalPrintString = "BB Count: %d\n";
      Constant *format_const = ConstantDataArray::getString(*Context, finalPrintString);
      BasicBlockPrintfFormatStr = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(finalPrintString)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "BasicBlockPrintfFormatStr");
      printf_func = printf_prototype(*Context, &M);
 
      errs() << "Module: " << M.getName() << "\n";
 
      return true;
    }
 
    //----------------------------------
    bool doFinalization(Module &M) {
    //all loops with an is_innermost value of true at this point are innermost loops
      for(int i; i < is_innermost.size(); i++ ){
      	if(is_innermost[i]){
      		errs() <<  printLoop(loop_vector[i], "Innermost Loop")<< '\n';
      	}
      }
      errs() << "-------Finished BasicBlocksDemo----------\n";
 
      return false;
    }

    //----------------------------------
    bool runOnFunction(Function &F) override {
    	int bbname_int=0;
      for(auto &BB: F) {
          std::string test="b"+(std::to_string(bbname_int));
          Twine bbname= Twine(test);
          BB.setName(bbname);
          bbname_int++;
      }

      DominatorTreeWrapperPass::runOnFunction(F);

      errs() << "Function: " << F.getName() << '\n';

      for(auto &BB: F) {
        // Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
        if(F.getName().equals("main") && isa<ReturnInst>(BB.getTerminator())) { // major hack?
          addFinalPrintf(BB, Context, bbCounter, BasicBlockPrintfFormatStr, printf_func);
        }
        runOnBasicBlock(BB);
      }

      //check all loops in loop vector to identify innermost loop
      for(int i=0; i<loop_vector.size(); i++){
      	if(is_innermost[i]){
	      	for(int j=0; j<loop_vector.size(); j++){
	      		if(j!=i){
	      			bool all_contained=true;
	      			for(auto &m : loop_vector.at(i)){
	      				if(loop_vector[j].find(m) == loop_vector.at(j).end()){
	      					all_contained=false;
	      					break;
	      				}

	      			}

	      			if(all_contained){
	      				is_innermost[j]=false;
	      			}
	      		}
	      	}
	    }
      }

 
      return true; 
    }

    bool runOnBasicBlock(BasicBlock &BB) {
      errs() << "BasicBlock: " << BB.getName() << '\n';
      IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
 
      Value *loadAddr = IRB.CreateLoad(bbCounter);
      Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
      IRB.CreateStore(addAddr, bbCounter);

      succ_iterator end = succ_end(&BB);
      for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit){
        //errs() << "Successor to "+BB.getName()+": " << sit->getName()<< '\n';

        //found a back edge
        if (getDomTree().dominates(sit->getTerminator(), &BB)){
        	std::stack<BasicBlock *> s;
        	std::set<BasicBlock *> loop;
      		loop.insert(*sit);
      		loop.insert(&BB);
      		s.push(&BB);

      		while(!s.empty()){

      			BasicBlock* m= s.top();
      			s.pop();
      			pred_iterator end_pred_iterator = pred_end(m);
      			for (pred_iterator pit = pred_begin(m);pit != end_pred_iterator; ++pit){
      				if(loop.find(*pit)==loop.end()){
      					s.push(*pit);
      					loop.insert(*pit);
      				}
      			}

      		}

      		//add loop to loop vector
      			loop_vector.push_back(loop);
      			is_innermost.push_back(true);

        }



      }
 
      for(auto &I: BB)
        errs() << I << "\n";
 
      return true;
    }

    std::string printLoop(std::set<BasicBlock *> loop, std::string label){
    	std::string formatted_loop=label+": {";
  		std::string comma="";
  		for(std::set<BasicBlock *>::iterator it=loop.begin(); it!=loop.end(); ++it){
  			formatted_loop=(formatted_loop+(comma+((*it)->getName()).str()));
  			comma=",";
  		}
  		formatted_loop+="}";

  		return formatted_loop;
    }

     //----------------------------------
    // Rest of this code is needed to: printf("%d\n", bbCounter); to the end of main, just BEFORE the return statement
    // For this, prepare the SCCGraph, and append to last BB?
    void addFinalPrintf(BasicBlock& BB, LLVMContext *Context, GlobalVariable *bbCounter, GlobalVariable *var, Function *printf_func) {
      IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
      std::vector<Constant*> indices;
      Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      indices.push_back(zero);
      indices.push_back(zero);
      Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 
      Value *bbc = builder.CreateLoad(bbCounter);
      CallInst *call = builder.CreateCall2(printf_func, var_ref, bbc);
      call->setTailCall(false);
    }

  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);

