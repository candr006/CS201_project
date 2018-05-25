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
#include "../Instrumentation/MaximumSpanningTree.h"
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

//Global variables these should be cleared after function run
    std::vector<std::set<BasicBlock *> > loop_vector;
    std::vector<bool> is_innermost;
    int num_not_visited=0;
    std::map<std::string, int> basic_block_key_map;
    std::map<std::string, int> num_paths;
    std::map<std::string, int> ball_larus_edge_values;
    std::vector<std::pair<BasicBlock*, BasicBlock*> > loop_head_tail;
    BasicBlock* innermost_loop_head;
    BasicBlock* innermost_loop_tail;
    MaximumSpanningTree<BasicBlock>::EdgeWeights ew_vector;
 
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


      //all loops with an is_innermost value of true at this point are innermost loops
    if(loop_vector.size()<1){
      errs() <<  "Innermost Loop: {}"<< '\n' << "Edge values: {}" << '\n';
    }
    std::set<BasicBlock *> innermost_loop;
    for(int i; i < is_innermost.size(); i++ ){
        if(is_innermost[i]){
          innermost_loop=loop_vector[i];
          innermost_loop_head=std::get<0>(loop_head_tail[i]);
          innermost_loop_tail=std::get<1>(loop_head_tail[i]);

          errs() <<  printLoop(loop_vector[i], "Innermost Loop")<< '\n';
        }
    //}
    else{
    //Get topological order of innermost loop
      std::vector<BasicBlock *> sorted_results2;
      std::vector<BasicBlock *> reversed_results;
      std::vector<bool> visited;
      //Hold whether the mark is temporary or permanent
      std::vector<std::string> mark_type;
      std::vector<BasicBlock *> innermost_loop_vector;
      

      std::set<BasicBlock *>::iterator it;
      int k=0;
      for (it=innermost_loop.begin(); it!=innermost_loop.end(); ++it){
        innermost_loop_vector.push_back(*it);
        basic_block_key_map.insert ( std::pair<std::string,int>((innermost_loop_vector[k])->getName().str(),k) );
        k++;
      }

      //keep track of how many basic blocks have not been visited yet
      num_not_visited=innermost_loop.size();
      
      // initialize visited vector to false
      //initialize mark type vector to empty string
      for (int i = 0; i < innermost_loop_vector.size(); i++){
          visited.push_back(false);
          mark_type.push_back("");
      }

      while(num_not_visited>0){
        for(int i=0; i<innermost_loop.size(); i++){
          if(!visited[i]){
            visitBlock(i, visited, mark_type, innermost_loop_vector, sorted_results2);
          }
        }
      }


      reversed_results=sorted_results2;
      errs() << printBBVector(sorted_results2,"Reverse Topological Sort") << '\n';


      //Ball Larus - Assign each path a unique value 
      /*for each vertex v in rev. top. order {
      if v is a leaf vertex { // no successors
        NumPaths(v) = 1;
      } else {
        NumPaths(v) = 0;
        for each edge e = v->w {
          Val(e) = NumPaths(v);
          NumPaths(v) += NumPaths(w);
        }
      }
    }*/
   // MaximumSpanningTree<BasicBlock>::EdgeWeights ew_vector;
      for(int i=0; i<reversed_results.size(); i++){
        int num_successors=0;
        succ_iterator end=succ_end(reversed_results[i]);
      for (succ_iterator sit = succ_begin(reversed_results[i]);sit != end; ++sit){
        if(innermost_loop.find(*sit)!=innermost_loop.end()){
            if ((*sit)!=innermost_loop_head){
              num_successors++;
            }
          }
      }

      
      std::string v_name=((reversed_results[i])->getName()).str();
      if(num_successors<1){
        num_paths[v_name]=1;
      }else{
        num_paths[v_name]=0;
        succ_iterator end=succ_end(reversed_results[i]);
        int edge_val= 0;
        for (succ_iterator sit = succ_begin(reversed_results[i]);sit != end; ++sit){
          if(innermost_loop.find(*sit)!=innermost_loop.end()){
            std::string w_name=(sit->getName()).str();
              if ((*sit)!=innermost_loop_head){
                std::string edge_name=v_name+" -> "+w_name;
                edge_val=num_paths[v_name];


                //edge
                //std::pair<BasicBlock*,BasicBlock*> e(reversed_results[i],*sit);
                MaximumSpanningTree<BasicBlock>::Edge e(reversed_results[i],*sit);
                //edge weight
                MaximumSpanningTree<BasicBlock>::EdgeWeight ew(e,edge_val);
                ew_vector.push_back(ew);

                ball_larus_edge_values[edge_name]=edge_val;
                num_paths[v_name]=(num_paths[v_name]+num_paths[w_name]);
              }
            }
        }
      }
      }

      MaximumSpanningTree<BasicBlock> mst (ew_vector);

      std::set<MaximumSpanningTree<BasicBlock>::Edge> edge_set;
      for(std::vector<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=mst.begin(); it!=mst.end();++it){
          edge_set.insert(*it);
      }

      //now identify the chords
      std::set<MaximumSpanningTree<BasicBlock>::Edge> chords;
      for(MaximumSpanningTree<BasicBlock>::EdgeWeights::iterator it=ew_vector.begin();it!=ew_vector.end();++it){
          if(edge_set.find(it->first)==edge_set.end()){
            chords.insert(it->first);
          }
      }




    //Step 2 of BL
    /* Register initialization code // 
    WS.add(ENTRY); 
    while not WS.emptyO { 
    vertex v = WS.removeO; 
    for each edge e = v->w 
      if e is a chord edge instrumentce, 'r=Inc(e)'); 
      else if e is the only incoming edge of w WS.add(w); 
      else instrumentte, 'r=O'); */
    std::stack<BasicBlock *> ws;
    ws.push(innermost_loop_head);

    while(!ws.empty()){
      BasicBlock * v= ws.top();
      ws.pop();
      for (succ_iterator sit = succ_begin(v);sit != succ_end(v); ++sit){
        BasicBlock* w= (*sit);
        MaximumSpanningTree<BasicBlock>::Edge e (v,w);
        //if e is a chord edge
        if(chords.find(e)!=chords.end()){
          //
        }
        else if(v->getTerminator()->getNumSuccessors()==1){
          ws.push(w);
        }else{
          //
        }

      }
    }


    //Memory Increment Code
    ws.push(innermost_loop_tail);
    while(!ws.empty()){
      BasicBlock * w= ws.top();
      ws.pop();

      for (pred_iterator pit = pred_begin(w);pit != pred_end(w); ++pit){
        BasicBlock* v= (*pit);
        MaximumSpanningTree<BasicBlock>::Edge e (v,w);
        //if e is a chord edge
        if(chords.find(e)!=chords.end()){
          //
        }
        else if(v->getTerminator()->getNumSuccessors()==1){
          ws.push(v);
        }else{
          //
        }

      }

    }

    //Register increment code
    //loop through uninstrumented chords


      //Print edge values
     errs() << "Edge Values: {" << '\n';
     for (std::map<std::string,int>::iterator it=ball_larus_edge_values.begin(); it!=ball_larus_edge_values.end(); ++it){
        errs() << " " << it->first << " => " << it->second << '\n';

      }
      errs() << "}" << '\n';

    }


    //basic_block_key_map.clear();
  }


    //clear global variables, each function will populate these
    is_innermost.clear();
    loop_vector.clear();

 
      return true; 
}

    void visitBlock(int i, std::vector<bool> &visited, std::vector<std::string> &mark_type, std::vector<BasicBlock *> loop,std::vector<BasicBlock*>&sorted_results2){
      //Recursive DFS

      if(mark_type[i]=="P"){
        return;
      }
      if(mark_type[i]=="T"){
        return;
      }
      mark_type[i]="T";

      succ_iterator end = succ_end(loop[i]);

     for (succ_iterator sit = succ_begin(loop[i]);sit != end; ++sit){
    //push visited block onto vector
      /*if (!(std::find(sorted_results2.begin(), sorted_results2.end(), loop[i]) != sorted_results2.end())){
        sorted_results2.push_back(loop[i]);
      }*/
      //if this is not a back edge, then visit
      int j= basic_block_key_map[sit->getName().str()];
      if (loop[j]!=innermost_loop_head){
        visitBlock(j, visited, mark_type, loop, sorted_results2); 
      }

    }

    mark_type[i]="P";
    sorted_results2.push_back(loop[i]);
    num_not_visited--;
    return;
}

void DFS(int events, BasicBlock* v, MaximumSpanningTree<BasicBlock>::Edge e, std::set<BasicBlock*> innermost_loop, std::set<MaximumSpanningTree<BasicBlock>::Edge> chords){
  for(pred_iterator pit =pred_begin(v); pit!=pred_end(v); ++pit){
      MaximumSpanningTree<BasicBlock>::Edge f(*pit,v);
      if(innermost_loop.find(*pit)!=innermost_loop.end() && (f!=e)){
        int Events=0;
        for(int i=0; i<ew_vector.size(); i++){
          if(ew_vector[i].first==f){
            Events=ew_vector[i].second;
          }
        }
        DFS((Dir(e,f)*events)+Events,(*pit),f, innermost_loop, chords);
      }
  }

  for(succ_iterator sit =succ_begin(v); sit!=succ_end(v); ++sit){
      MaximumSpanningTree<BasicBlock>::Edge f(*sit,v);
      if(innermost_loop.find(*sit)!=innermost_loop.end() && (f!=e)){
        int Events=0;
        for(int i=0; i<ew_vector.size(); i++){
          if(ew_vector[i].first==f){
            Events=ew_vector[i].second;
          }
        }
        DFS((Dir(e,f)*events)+Events,(*sit),f, innermost_loop, chords);
      }
  }

  //loop through chords std::set<MaximumSpanningTree<BasicBlock>::Edge> chords;
  for(std::set<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=chords.begin(); it!=chords.end(); ++it){
    //v1=src(f) -> (*it).first;
    //v2=tgt(f) -> (*it).second;


  }



  return;
}


int Dir(MaximumSpanningTree<BasicBlock>::Edge e, MaximumSpanningTree<BasicBlock>::Edge f){
  if(e.first==NULL || e.second==NULL){
    return 1;
  }else if(e.first==f.second ||f.first==e.second){
    return 1;
  }else{
    return -1;
  }
}

    bool runOnBasicBlock(BasicBlock &BB) {
      errs() << "BasicBlock: " << BB.getName() << '\n';
      IRBuilder<> IRB(BB.getFirstInsertionPt()); // Will insert the generated instructions BEFORE the first BB instruction
 
      Value *loadAddr = IRB.CreateLoad(bbCounter);
      Value *addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
      IRB.CreateStore(addAddr, bbCounter);

      succ_iterator end = succ_end(&BB);
      for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit){

        //found a back edge
        //Loop Head: sit->getTerminator
        //Loop Tail: &BB 
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
            BasicBlock * head=(*sit);
            BasicBlock * tail= &BB;
          std::pair <BasicBlock*, BasicBlock*> head_tail (head,tail);           
          loop_head_tail.push_back(head_tail);
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

    std::string printBBVector(std::vector<BasicBlock*> v, std::string label){
      std::string formatted_loop=label+": {";
      std::string comma="";
      for(int i=0; i<v.size(); i++){
        formatted_loop=(formatted_loop+(comma+(v[i]->getName().str())));
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