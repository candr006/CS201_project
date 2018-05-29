/*
 * Authors: 
 * Claudia Andrade (candr006@ucr.edu)
 * Daniel Handojo (dhand002@ucr.edu)
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
    // Page 7 of ball-larus algorithm
    struct MemCountContainer {
      int increment;
      bool includeR;
      MemCountContainer() : increment(0), includeR(false) {}
      MemCountContainer(int i, bool b) : increment(i), includeR(b) {}
    };

    struct LoopDetails {
      AllocaInst *pathCntMem; // Pointer to count array
      std::set<std::string> loopBlocks;  // blocks in loop
      BasicBlock *loop_header;  // Entry/head node of loop
      int numPaths;           // Number of paths from head to tail
      LoopDetails() : pathCntMem(NULL), loop_header(NULL), numPaths(0) {}
      // No constructor for allocaInst (this is set after processing function)
      LoopDetails(BasicBlock* b, int n) : pathCntMem(NULL), loop_header(b), numPaths(n) {}
    };

    static char ID;
    LLVMContext *Context;

    Function *printf_func = NULL;

    // For edge profiling
    GlobalVariable *edge_cnt_array = NULL;
    GlobalVariable *edgeFormatStr1 = NULL;
    GlobalVariable *edgeFormatStr2 = NULL;
    GlobalVariable *zeroVar = NULL;

    // Path profiling variables
    GlobalVariable *rVar = NULL;
    GlobalVariable *pathFormatStr1 = NULL;
    GlobalVariable *pathFormatStr2 = NULL;
    std::vector<LoopDetails> loopDetails; // clear after function

    //Global variables these should be cleared after function run
    std::vector<std::set<BasicBlock *> > loop_vector;
    std::vector<bool> is_innermost;
    int num_not_visited=0;
    std::map<std::string, int> basic_block_key_map;
    std::map<std::string, int> num_paths;
    std::map<std::string, int> ball_larus_edge_values;
    std::vector<std::pair<BasicBlock*, BasicBlock*> > loop_header_tail;
    BasicBlock* innermost_loop_header;
    BasicBlock* innermost_loop_tail;
    MaximumSpanningTree<BasicBlock>::EdgeWeights ew_vector;
    std::map<MaximumSpanningTree<BasicBlock>::Edge, double> r_eq_path_instrumentation;
    std::map<MaximumSpanningTree<BasicBlock>::Edge, double> r_plus_eq_path_instrumentation;
    std::map<MaximumSpanningTree<BasicBlock>::Edge, struct MemCountContainer> count_path_instrumentation;

    int debug_dfs=1;
 
    //----------------------------------
    bool doInitialization(Module &M) {
      errs() << "\n---------Starting BasicBlockDemo---------\n";
      Context = &M.getContext();
      Constant *format_const;
      printf_func = printf_prototype(*Context, &M);

      // Edge Profiling Setup
      // edge str 1 and 2
      const char *edgeStr1 = "EDGE PROFILING:\n";
      format_const = ConstantDataArray::getString(*Context, edgeStr1);
      edgeFormatStr1 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(edgeStr1)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "edgeFormatStr1");

      const char *edgeStr2 = "b%d -> b%d: %d\n";
      format_const = ConstantDataArray::getString(*Context, edgeStr2);
      edgeFormatStr2 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(edgeStr2)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "edgeFormatStr2");

      // Path Profiling Setup
      // path str 1 and 2
      const char *pathStr1 = "PATH PROFILING:\n";
      format_const = ConstantDataArray::getString(*Context, pathStr1);
      pathFormatStr1 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(pathStr1)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "pathFormatStr1");

      const char *pathStr2 = "Path_b%d_%d: %d\n";
      format_const = ConstantDataArray::getString(*Context, pathStr2);
      pathFormatStr2 = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 8), 
          strlen(pathStr2)+1), true, llvm::GlobalValue::PrivateLinkage, format_const, "pathFormatStr2");

      // order stays the same because the for loop stays the same. Then just make an array for the largest edge 
      // count. 
      int max_num_edges = 0;
      int num_edges = 0;
      // Go through each function
      for (auto& f : M) {
        // Go through each bb
        for (auto& bb : f) {
          // go through successors of bb
          succ_iterator end = succ_end(&bb);
          for (succ_iterator sit = succ_begin(&bb);sit != end; ++sit) {
            num_edges++;  
          }
        }
        if (num_edges > max_num_edges) max_num_edges = num_edges;
      }

      // edge_cnt_array: Declaring the actual int array of size max_num_blocks
      llvm::ArrayType* edgeArrayType = llvm::ArrayType::get(llvm::IntegerType::get(*Context, 32), max_num_edges);
      edge_cnt_array = new GlobalVariable(M, llvm::ArrayType::get(llvm::IntegerType::get(*Context, 32), max_num_edges), 
          false, llvm::GlobalValue::PrivateLinkage, ConstantArray::get(edgeArrayType, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0)), "edge_cnt_array");

      // zero var and r (same value for now)
      zeroVar = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::PrivateLinkage, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0), "zeroVar");
      rVar = new GlobalVariable(M, Type::getInt32Ty(*Context), false, GlobalValue::PrivateLinkage, 
          ConstantInt::get(Type::getInt32Ty(*Context), 0), "rVar");

      //errs() << "Module: " << M.getName() << "\n";

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

      DominatorTreeWrapperPass::runOnFunction(F); // Custom use of DominatorTreeFunctionPass

      errs() << "Function: " << F.getName() << '\n';

      for(auto &BB: F) {
        // Add the footer to Main's BB containing the return 0; statement BEFORE calling runOnBasicBlock
        runOnBasicBlock(BB);
      }

      // ----------Our code is below------------
      //check all loops in loop vector to identify innermost loop
      for(unsigned int i=0; i<loop_vector.size(); i++){
        if(is_innermost[i]){
          for(unsigned int j=0; j<loop_vector.size(); j++){
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
for(unsigned int i = 0; i < is_innermost.size(); i++ ){
    if(is_innermost[i]){
      innermost_loop=loop_vector[i];
      innermost_loop_header=std::get<0>(loop_header_tail[i]);
      innermost_loop_tail=std::get<1>(loop_header_tail[i]);

      errs() <<  printLoop(loop_vector[i], "Innermost Loop")<< '\n';

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
      for(unsigned int i = 0; i < innermost_loop_vector.size(); i++){
          visited.push_back(false);
          mark_type.push_back("");
      }

      while(num_not_visited>0){
        for(unsigned int i=0; i<innermost_loop.size(); i++){
          if(!visited[i]){
            visitBlock(i, visited, mark_type, innermost_loop_vector, sorted_results2);
          }
        }
      }


      reversed_results=sorted_results2;


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
      // Path profiling variables
      LoopDetails loopData;
      loopData.loop_header = innermost_loop_header;
      int num_loop_exits=0;
      std::map<BasicBlock*, int> loop_exit_edges;
      for(unsigned int i=0; i<reversed_results.size(); i++){
          int num_successors=0;
          succ_iterator end=succ_end(reversed_results[i]);
        for (succ_iterator sit = succ_begin(reversed_results[i]);sit != end; ++sit){
          if(innermost_loop.find(*sit)!=innermost_loop.end()){
              if ((*sit)!=innermost_loop_header){
                num_successors++;
              }
            }
        }

        
        std::string v_name=((reversed_results[i])->getName()).str();
        //keep a count of how many loop exits there are per vertex
        
        if(num_successors<1){
          num_paths[v_name]=1;
        }else{
          num_paths[v_name]=0;
          succ_iterator end=succ_end(reversed_results[i]);
          int edge_val= 0;
          for (succ_iterator sit = succ_begin(reversed_results[i]);sit != end; ++sit){
            if(innermost_loop.find(*sit)!=innermost_loop.end()){
              std::string w_name=(sit->getName()).str();
                if ((*sit)!=innermost_loop_header){
                  std::string edge_name=v_name+" -> "+w_name;
                  edge_val=num_paths[v_name];
                  ball_larus_edge_values[edge_name]=edge_val;
                  num_paths[v_name]=(num_paths[v_name]+num_paths[w_name]);

                  // Save loop contents in loop details 
                  loopData.loopBlocks.insert(v_name);
                  loopData.loopBlocks.insert(w_name);
                }
              }else{
                num_loop_exits++;
                //create a set of loop exit edges
                if(loop_exit_edges.find(reversed_results[i])!=loop_exit_edges.end()){
                  loop_exit_edges[reversed_results[i]]++;
                }else{
                  loop_exit_edges[reversed_results[i]]=1;
                }
              }
          }
        }
      }

      // Push path profiling details to vector
      loopData.numPaths = num_paths[innermost_loop_header->getName().str()];
      loopDetails.push_back(loopData);

  std::reverse(sorted_results2.begin(),sorted_results2.end());
  //Approx. edge frequencies
  int loop_mult=10;
  double loop_exit_weight=(1.0/num_loop_exits);
    std::map<BasicBlock*, double> vertex_weight;
   std::map<MaximumSpanningTree<BasicBlock>::Edge, double> apprx_edge_weight;
  //initialize loop head vert weight to 1* loop multiplier
  
  for(unsigned int i=0; i<sorted_results2.size(); i++){
    double w_e;
    if(loop_exit_edges.find(sorted_results2[i])!=loop_exit_edges.end()){
      w_e=(loop_exit_weight*loop_exit_edges[sorted_results2[i]]);
    }else{
      //no exit edges
      w_e=0;
    }

    vertex_weight[sorted_results2[i]]=0;
    if(sorted_results2[i]!=innermost_loop_header){

      for (pred_iterator pit = pred_begin(sorted_results2[i]);pit != pred_end(sorted_results2[i]); ++pit){
        if(innermost_loop.find(*pit)!=innermost_loop.end()){
          //basic block is in the loop 
          MaximumSpanningTree<BasicBlock>::Edge e(*pit,sorted_results2[i]);
          vertex_weight[sorted_results2[i]]=vertex_weight[sorted_results2[i]]+apprx_edge_weight[e];           
        }
        
      }
    }else{
      vertex_weight[innermost_loop_header]=1*loop_mult;
    }

    for (succ_iterator sit = succ_begin(sorted_results2[i]);sit != succ_end(sorted_results2[i]); ++sit){
      double w= vertex_weight[sorted_results2[i]];
      if(innermost_loop.find(*sit)!=innermost_loop.end()){
        //basic block is in the loop 
        MaximumSpanningTree<BasicBlock>::Edge out_edge(sorted_results2[i],*sit);

        double n=sorted_results2[i]->getTerminator()->getNumSuccessors();
        if(loop_exit_edges.find(sorted_results2[i])!=loop_exit_edges.end()){
          n=n-loop_exit_edges[sorted_results2[i]];
        }

        apprx_edge_weight[out_edge]=(w-w_e)/n;
      }
    }
  }


    for(std::map<MaximumSpanningTree<BasicBlock>::Edge,double>::iterator it=apprx_edge_weight.begin(); it!=apprx_edge_weight.end(); ++it){

        MaximumSpanningTree<BasicBlock>::EdgeWeight ew((*it).first,(*it).second);
        ew_vector.push_back(ew);
    }


// Add back edge to the ew_vector
    std::string v_name=innermost_loop_tail->getName();
    std::string w_name=innermost_loop_header->getName();
    MaximumSpanningTree<BasicBlock>::Edge e_be(innermost_loop_tail,innermost_loop_header);
    //edge weight
    MaximumSpanningTree<BasicBlock>::EdgeWeight ew_be(e_be,1);
    ew_vector.push_back(ew_be);

     //Print edge values
    //Edge values: {(b1,b3,0),(b3,b4,0),(b3,b5,1),(b4,b6,0),(b5,b6,0)}
   errs() << "Edge Values: {" ;
   std::string comm="";
   for (std::map<std::string,int>::iterator it=ball_larus_edge_values.begin(); it!=ball_larus_edge_values.end(); ++it){
      std::string s=it->first;
      std::string delimiter = " -> ";
      std::string e1 = s.substr(0, s.find(delimiter));
      std::string e2 = s.substr(s.find(delimiter)+4);
      errs() << comm<<"(" << e1 <<"," << e2 <<"," << it->second <<")";
      comm=",";

    }
    errs() << "}" << "\n\n";


      MaximumSpanningTree<BasicBlock> mst (ew_vector);

      std::set<MaximumSpanningTree<BasicBlock>::Edge> edge_set;
      for(std::vector<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=mst.begin(); it!=mst.end();++it){
          edge_set.insert(*it);
        
      }

      //now identify the chords
      std::set<MaximumSpanningTree<BasicBlock>::Edge> chords;
      for(MaximumSpanningTree<BasicBlock>::EdgeWeights::iterator it=ew_vector.begin();it!=ew_vector.end();++it){
          MaximumSpanningTree<BasicBlock>::Edge e(it->first);
          std::string edge_name=e.first->getName().str()+" -> "+e.second->getName().str();
          int bev=ball_larus_edge_values[edge_name];
          //Reset edge weight to original ball larus edge vals
          it->second=bev;

          if(edge_set.find(it->first)==edge_set.end()){
            chords.insert(it->first);
          }

      }


      //Initialize increment code for chords
    //Use map for chord increments

    std::map<MaximumSpanningTree<BasicBlock>::Edge, int> increment;
    for(std::set<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=chords.begin(); it!=chords.end(); ++it){
        increment[*it]=0;
    }
    //DFS(0,root,null) goes here
    //NULL not accepted for edge so passing in an empty edge
    MaximumSpanningTree<BasicBlock>::Edge null_edge (NULL,NULL);
    DFS(0,innermost_loop_header,null_edge, innermost_loop, chords, increment, innermost_loop_tail, innermost_loop_header);

    //next loop through chords goes here
    for(std::set<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=chords.begin(); it!=chords.end(); ++it){
        int Events=0;
        for(unsigned int i=0; i<ew_vector.size(); i++){
          if(ew_vector[i].first==(*it)){
            Events=ew_vector[i].second;
          }
        }
        increment[*it]=increment[*it]+Events;
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
    ws.push(innermost_loop_header);

    while(!ws.empty()){
      BasicBlock * v= ws.top();
      ws.pop();
      for (succ_iterator sit = succ_begin(v);sit != succ_end(v); ++sit){
        if(innermost_loop.find(*sit)!=innermost_loop.end()){
          BasicBlock* w= (*sit);
          MaximumSpanningTree<BasicBlock>::Edge e (v,w);
          //if e is a chord edge
          if(chords.find(e)!=chords.end()){
            r_eq_path_instrumentation[e]=increment[e];
          }
          else if(v->getTerminator()->getNumSuccessors()==1){
            ws.push(w);
          }else{
            r_eq_path_instrumentation[e]=0;
          }
      }
      }
    }


    //Memory Increment Code
    ws.push(innermost_loop_tail);
    while(!ws.empty()){
      BasicBlock * w= ws.top();
      ws.pop();

      for (pred_iterator pit = pred_begin(w);pit != pred_end(w); ++pit){
        if(innermost_loop.find(*pit)!=innermost_loop.end()){
          BasicBlock* v= (*pit);
          MaximumSpanningTree<BasicBlock>::Edge e (v,w);
          //if e is a chord edge
          if(chords.find(e)!=chords.end()){
           if(r_eq_path_instrumentation[e]==increment[e]){
              count_path_instrumentation[e]=MemCountContainer(increment[e],false);
            }else{
            count_path_instrumentation[e]=MemCountContainer(increment[e],true);
            }
          }
          else if(v->getTerminator()->getNumSuccessors()==1){
            ws.push(v);
          }else{
            count_path_instrumentation[e]=MemCountContainer(0,true);
          }
      }
      }

    }

    //Register increment code
    //loop through uninstrumented chords
    for(std::set<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=chords.begin(); it!=chords.end(); ++it){
      bool not_in_any_path_instrumentation=true;
      if(r_eq_path_instrumentation.find(*it)!=r_eq_path_instrumentation.end()){
        not_in_any_path_instrumentation=false;
      }
      if(count_path_instrumentation.find(*it)!=count_path_instrumentation.end()){
        not_in_any_path_instrumentation=false;
      }

      if(not_in_any_path_instrumentation){
        r_plus_eq_path_instrumentation[*it]=increment[*it];
      }
    }

      //end of is_innermost[i] if loop - code above will be repeated for each innermost loop
      //clear global variables
      ball_larus_edge_values.clear();
      basic_block_key_map.clear();
      num_not_visited=0;
      num_paths.clear();
      ew_vector.clear();
    }
  }

      // Add edge profiling code to CFG. (Adds a ton of extra basicBlocks, so I want to do this after
      // path profiling).
      insertAllEdgeNodes(F);
      insertEdgeInstrumentation(F);
      insertPathInstrumentation(F);

      // add printf calls for Edge Profile instrumentation
      addEdgeProfilePrints(F, printf_func);
      addPathProfilePrints(F, printf_func);

      //clear global variables, each function will populate these
      is_innermost.clear();
      loop_vector.clear();
      basic_block_key_map.clear();
      loopDetails.clear();
      r_eq_path_instrumentation.clear();
      count_path_instrumentation.clear();
      r_plus_eq_path_instrumentation.clear();
      ball_larus_edge_values.clear();
      loop_header_tail.clear();

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
      if (loop[j]!=innermost_loop_header){
        visitBlock(j, visited, mark_type, loop, sorted_results2); 
      }

    }

    mark_type[i]="P";
    sorted_results2.push_back(loop[i]);
    num_not_visited--;
    return;
}

void DFS(int events, BasicBlock* v, MaximumSpanningTree<BasicBlock>::Edge e, std::set<BasicBlock*> innermost_loop, 
  std::set<MaximumSpanningTree<BasicBlock>::Edge> chords, std::map<MaximumSpanningTree<BasicBlock>::Edge,int> &increment,
  BasicBlock* innermost_loop_tail, BasicBlock* innermost_loop_header){

//if(debug_dfs<50){
  for(pred_iterator pit =pred_begin(v); pit!=pred_end(v); ++pit){
      MaximumSpanningTree<BasicBlock>::Edge f(*pit,v);
      if(innermost_loop.find(*pit)!=innermost_loop.end() && (*pit)!=innermost_loop_tail && (chords.find(f)==chords.end())){
        if((f!=e)){
          int Events=0;
          for(unsigned int i=0; i<ew_vector.size(); i++){
            if(ew_vector[i].first==f){
              Events=ew_vector[i].second;
            }
          }
          debug_dfs++;
          DFS((Dir(e,f)*events)+Events,(*pit),f, innermost_loop, chords, increment, innermost_loop_tail, innermost_loop_header);
      }
     }
  }

  for(succ_iterator sit =succ_begin(v); sit!=succ_end(v); ++sit){
      MaximumSpanningTree<BasicBlock>::Edge f(v,*sit);
      if((innermost_loop.find(*sit)!=innermost_loop.end()) && (f!=e) && ((*sit)!=innermost_loop_header) && (chords.find(f)==chords.end())){
        int Events=0;
        for(unsigned int i=0; i<ew_vector.size(); i++){
          if(ew_vector[i].first==f){
            Events=ew_vector[i].second;
            break;
          }
        }
        debug_dfs++;

        DFS((Dir(e,f)*events)+Events,(*sit),f, innermost_loop, chords, increment, innermost_loop_tail, innermost_loop_header);
      }
  }

  //loop through chords std::set<MaximumSpanningTree<BasicBlock>::Edge> chords;
  for(std::set<MaximumSpanningTree<BasicBlock>::Edge>::iterator it=chords.begin(); it!=chords.end(); ++it){
    const BasicBlock* v1=(*it).first;
    const BasicBlock* v2=(*it).second;
    MaximumSpanningTree<BasicBlock>::Edge f=(*it);

    if(v==v1 || v==v2){
      increment[f]=increment[f]+(Dir(e,f)*events);

    }

  }


//}
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
          loop_header_tail.push_back(head_tail);
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
      for(unsigned int i=0; i<v.size(); i++){
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
    // Copy of above function for various integer arguments to print. Named after CreateCall2 style
    // MUST PASS IRBuilder OBJECT TO THESE
    void addFinalPrintf3(BasicBlock& BB, LLVMContext *Context, Value *arg1, Value *arg2, 
          Value *arg3, GlobalVariable *var, Function *printf_func) {
      IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
      std::vector<Constant*> indices;
      Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      indices.push_back(zero);
      indices.push_back(zero);
      Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 
      CallInst *call = builder.CreateCall4(printf_func, var_ref, arg1, arg2, arg3);
      call->setTailCall(false);
    }

    void addFinalPrintf0(BasicBlock& BB, LLVMContext *Context, GlobalVariable *var, Function *printf_func) {
      IRBuilder<> builder(BB.getTerminator()); // Insert BEFORE the final statement
      std::vector<Constant*> indices;
      Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(*Context));
      indices.push_back(zero);
      indices.push_back(zero);
      Constant *var_ref = ConstantExpr::getGetElementPtr(var, indices);
 
      CallInst *call = builder.CreateCall(printf_func, var_ref);
      call->setTailCall(false);
    }

    void addEdgeProfilePrints(Function& F, Function *printf_func) {
      // Don't run for functions with no edges
      if (F.size() <= 1)
        return;

      // Get exit block for function F (need for IRBuilder hack)
      BasicBlock* exitBlock = NULL;
      for(auto &B: F) {
        if(isa<ReturnInst>(B.getTerminator())) { 
          exitBlock = &B;
        }
      }

      // Output first line
      IRBuilder<> IRB(exitBlock->getTerminator()); // Insert BEFORE the final statement
      addFinalPrintf0(*exitBlock, Context, edgeFormatStr1, printf_func);

      // Load zero into Value*
      Value* zeroVarVal = IRB.CreateLoad(zeroVar);

      // Output each edge
      for (auto& BB : F) {
        std::string bbname = BB.getName();

        // Only look at edge nodes
        if (bbname.size() >= 7 && bbname.substr(0,7) == "bb_edge") {
          // Get edge count into Value*
          const char* nodeName = bbname.c_str();
          int64_t nodeIdx = std::atoi(nodeName + 7); // ignore "bb_edge"
          Value *edgeCnt = getEdgeFreq(IRB, nodeIdx);

          // Get source node index into Value*
          nodeName = BB.getUniquePredecessor()->getName().str().c_str();
          nodeIdx = std::atoi(nodeName + 1); // ignore 'b'
          Value* srcIndex = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), nodeIdx), zeroVarVal);

          // Get dst node index into Value*
          nodeName = BB.getTerminator()->getSuccessor(0)->getName().str().c_str();
          nodeIdx = std::atoi(nodeName + 1); // ignore 'b'
          Value* dstIndex = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), nodeIdx), zeroVarVal);

          // Print edge count
          addFinalPrintf3(*exitBlock, Context, srcIndex, dstIndex, edgeCnt, edgeFormatStr2, printf_func);
        }
      }
    }

    Value* getEdgeFreq(IRBuilder<> IRB, int blockIdx) {
      Value* idxList[2] = {
        ConstantInt::get(Type::getInt32Ty(*Context), 0), 
        ConstantInt::get(Type::getInt32Ty(*Context), blockIdx)
      };
      Value *bbPtr = IRB.CreateGEP(edge_cnt_array, ArrayRef<Value*>(idxList, 2));
      return IRB.CreateLoad(bbPtr);
    }

    Value* getEdgeFreqPtr(IRBuilder<> IRB, int blockIdx) {
      Value* idxList[2] = {
        ConstantInt::get(Type::getInt32Ty(*Context), 0), 
        ConstantInt::get(Type::getInt32Ty(*Context), blockIdx)
      };
      return IRB.CreateGEP(edge_cnt_array, ArrayRef<Value*>(idxList, 2));
    }

    Value* getArrayPtr(IRBuilder<> IRB, Value *ptr, Value *index) {
      // The first 0 index is required because (if I recall) LLVM makes even the variable 
      // access an "array" access, so we need to access the array, then the array element
      Value* idxList[2] = {
        ConstantInt::get(Type::getInt32Ty(*Context), 0), 
        index
      };
      return IRB.CreateGEP(ptr, ArrayRef<Value*>(idxList, 2));
    }

    void insertEdgeInstrumentation(Function &F) {
      // Count # of edges in function
      int num_edges = 0;
      for (auto& bb : F) {
        succ_iterator end = succ_end(&bb);
        for (succ_iterator sit = succ_begin(&bb);sit != end; ++sit) {
          num_edges++;  
        }
      }
      IRBuilder<> startBlockIRB(F.getEntryBlock().begin());
      setArrayToZeroes(startBlockIRB, edge_cnt_array, num_edges); // clear array

      for (auto &BB : F) {
        std::string bbname = BB.getName().str();

        // Only look at non-edge nodes
        if (bbname.size() < 7 || bbname.substr(0,7) != "bb_edge") {
          // Iterate through connected edge nodes (always children of regular nodes)
          // Inserts instrumentation node for each edge
          succ_iterator end = succ_end(&BB);
          for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit) {
            IRBuilder<> IRB(sit->begin());
            Value* loadAddr = IRB.CreateLoad(zeroVar);

            // Get successor index into Value*
            const char* blockName = sit->getName().str().c_str();
            int64_t blockIdx = std::atoi(blockName + 7); // ignore "bb_edge"

            // Get array elem ptr edge count into Value*
            Value *edgePtr = getEdgeFreqPtr(IRB, blockIdx);
            loadAddr = IRB.CreateLoad(edgePtr);

            // Access array and increment count
            Value* addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), loadAddr);
            IRB.CreateStore(addAddr, edgePtr);
          }
        } 
      }
    }

    void insertPathInstrumentation(Function &F) {
      for (auto &loop : loopDetails) {
        insertLoopPathInstrumentation(F, loop);
      }
    }

    void insertLoopPathInstrumentation(Function &F, LoopDetails &loop) {
      // Create "local" array in the stack (llvm.org/docs/tutorial/ocamllangimpl7.html)
      IRBuilder<> pathIRB(F.getEntryBlock().begin());
      llvm::ArrayType* pathCntArrayType = llvm::ArrayType::get(
          llvm::IntegerType::get(*Context, 32), loop.numPaths);
      // Save it to loop details
      loop.pathCntMem = pathIRB.CreateAlloca(pathCntArrayType, 
          ConstantInt::get(Type::getInt32Ty(*Context), loop.numPaths), "path_cnt_array");

      setArrayToZeroes(pathIRB, loop.pathCntMem, loop.numPaths); // clear array

      for (auto &BB : F) {
        std::string bbname = BB.getName().str();

        // Only look at non-edge nodes in the loop
        if (loop.loopBlocks.find(bbname) != loop.loopBlocks.end()) {
          // Iterate through connected edge nodes (always children of regular nodes)
          // Inserts instrumentation node for each edge
          succ_iterator end = succ_end(&BB);
          for (succ_iterator sit = succ_begin(&BB);sit != end; ++sit) {
            IRBuilder<> IRB(sit->begin());
            Value* zeroAddr = IRB.CreateLoad(zeroVar);  

            // Remember, the edge node connects two "original" nodes
            auto e = MaximumSpanningTree<BasicBlock>::Edge(&BB, sit->getTerminator()->getSuccessor(0));

            // "r=Inc(e)" or "r=0"
            if (r_eq_path_instrumentation.find(e) != r_eq_path_instrumentation.end()) {
              Value* addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), (int) r_eq_path_instrumentation[e]), zeroAddr);
              IRB.CreateStore(addAddr, rVar);
            }

            // "count[Inc(e)]++" or "count[r+Inc(e)]++" or "count[r]++"
            if (count_path_instrumentation.find(e) != count_path_instrumentation.end()) {
              Value* addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 
                  count_path_instrumentation[e].increment), zeroAddr);

              if (count_path_instrumentation[e].includeR) {
                Value* rAddr = IRB.CreateLoad(rVar);
                addAddr = IRB.CreateAdd(addAddr, rAddr);
              }

              // is this incorrect code (using alloca instr as ptr to array)? Unsure about this
              Value *pathCntPtr = getArrayPtr(IRB, loop.pathCntMem, addAddr);
              Value *pathCntVar = IRB.CreateLoad(pathCntPtr);  

              // increment count[~] & store back into array
              addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 1), pathCntVar);
              IRB.CreateStore(addAddr, pathCntPtr);
            }

            // "r+=Inc(c)"
            if (r_plus_eq_path_instrumentation.find(e) != r_plus_eq_path_instrumentation.end()) {
              Value* rAddr = IRB.CreateLoad(rVar);
              Value* addAddr = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), 
                  (int) r_plus_eq_path_instrumentation[e]), rAddr);
              IRB.CreateStore(addAddr, rVar);
            }
          }
        } 
      }
    }

    void setArrayToZeroes(IRBuilder<> IRB, Value *array, const int size) {
      // zero variable to store in array locations
      Value* zeroAddr = IRB.CreateLoad(zeroVar);  

      // store zero in each array element
      for(int i = 0; i < size; i++) {
        // Array index
        Value* indexVal = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), i), zeroAddr);

        // get array element pointer
        Value *pathCntPtr = getArrayPtr(IRB, array, indexVal);

        // store zeroVar into pointer
        IRB.CreateStore(zeroAddr, pathCntPtr);
      }
    }

    void insertAllEdgeNodes(Function &F) {
      for (auto& BB : F) {
        std::string bbname = BB.getName();

        if (bbname.length() < 7 || bbname.substr(0, 7) != "bb_edge") {
          succ_iterator end = succ_end(&BB);

          // Iterate through successors and split edges
          for (succ_iterator sit = succ_begin(&BB); sit != end; ++sit) {
            // Is not an edge node
            if (sit->getName().str().length() < 7 || sit->getName().str().substr(0, 7) != "bb_edge") {
              insertEdgeNode(bbname, *sit);
            }
          }
        }
      }

      fixAllEdgeReferences();
    }

    void fixAllEdgeReferences() {
      // Copies of variables with edge references that need fixixing
      // Using copies to avoid iterator issues when removing old versions
      std::map<MaximumSpanningTree<BasicBlock>::Edge, double> r_eq_copy;
      std::map<MaximumSpanningTree<BasicBlock>::Edge, double> r_plus_eq_copy;
      std::map<MaximumSpanningTree<BasicBlock>::Edge, struct MemCountContainer> count_copy;

      for (auto &rSet : r_eq_path_instrumentation) {
        auto correctE = MaximumSpanningTree<BasicBlock>::Edge(
            rSet.first.first->getTerminator()->getSuccessor(0),
            rSet.first.second->getTerminator()->getSuccessor(0));

        // Swap old edge with corrected edge
        r_eq_copy[correctE] = rSet.second;
      }

      for (auto &memVar : count_path_instrumentation) {
        auto correctE = MaximumSpanningTree<BasicBlock>::Edge(
            memVar.first.first->getTerminator()->getSuccessor(0),
            memVar.first.second->getTerminator()->getSuccessor(0));

        // Swap old edge with corrected edge
        count_copy[correctE] = memVar.second;
      }

      for (auto &rPlusSet : r_plus_eq_path_instrumentation) {
        auto correctE = MaximumSpanningTree<BasicBlock>::Edge(
            rPlusSet.first.first->getTerminator()->getSuccessor(0),
            rPlusSet.first.second->getTerminator()->getSuccessor(0));

        // Swap old edge with corrected edge
        r_plus_eq_copy[correctE] = rPlusSet.second;
      }

      // replace originals with fixed copies
      r_eq_path_instrumentation = r_eq_copy;
      count_path_instrumentation = count_copy;
      r_plus_eq_path_instrumentation = r_plus_eq_copy;
    }

    void insertEdgeNode(std::string srcNodeName, BasicBlock* currDstNode) {
      Twine edgeName = Twine("bb_edge");

      // The child becomes the "edge" node (save name to give to child node)
      std::string succName = currDstNode->getName();
      currDstNode->setName(edgeName);

      // The newly split node becomes the "child" node because split
      // gives the instructions to the new node 
      BasicBlock *newDstNode = currDstNode->splitBasicBlock(currDstNode->begin(), succName);

      // Fix predecessors to point to node still, not to edge
      pred_iterator end_pred_iterator = pred_end(currDstNode);
      for (pred_iterator pit = pred_begin(currDstNode);pit != end_pred_iterator; ++pit) {
        // Change successors of nodes besides the current node
        if ((*pit)->getName().str() != srcNodeName) {
          // Iterate through successors of the predecessor node (only want to change 1 successor)
          TerminatorInst* terminator = (*pit)->getTerminator();
          for(unsigned int i = 0; i < terminator->getNumSuccessors(); i++) {
            if (terminator->getSuccessor(i)->getName() == currDstNode->getName()) {
              terminator->setSuccessor(i, newDstNode);
              break;
            }
          }
        }
      }
    }

    void addPathProfilePrints(Function &F, Function *printf_func) {
      // Don't run if there are no paths to print
      if (loopDetails.empty())
        return;

      // Get exit block for function F (need for IRBuilder hack)
      BasicBlock* exitBlock = NULL;
      for(auto &B: F) {
        if(isa<ReturnInst>(B.getTerminator())) { 
          exitBlock = &B;
        }
      }

      // Output first line
      IRBuilder<> IRB(exitBlock->getTerminator()); // Insert BEFORE the final statement
      addFinalPrintf0(*exitBlock, Context, pathFormatStr1, printf_func);

      // Output profile for each loop's paths
      for (auto &loop : loopDetails) {
        for(int i = 0; i < loop.numPaths; i++) {
          // Super helpful zero variable
          Value* zeroAddr = IRB.CreateLoad(zeroVar);  

          // Get loop header's block index
          const char* blockName = loop.loop_header->getTerminator()
              ->getSuccessor(0)->getName().str().c_str();
          int64_t blockIdx = std::atoi(blockName + 1); // ignore 'b'
          Value* blockIdxVal = IRB.CreateAdd(ConstantInt::get(
              Type::getInt32Ty(*Context), blockIdx), zeroAddr);

          // Get path index
          Value* pathIdxVal = IRB.CreateAdd(ConstantInt::get(Type::getInt32Ty(*Context), i), zeroAddr);

          // Get path counter
          Value *pathCntPtr = getArrayPtr(IRB, loop.pathCntMem, pathIdxVal);
          Value *pathCntVar = IRB.CreateLoad(pathCntPtr);  

          addFinalPrintf3(*exitBlock, Context, blockIdxVal, pathIdxVal, 
              pathCntVar, pathFormatStr2, printf_func);
        }
      }
    }
  };
}

char CS201PathProfiling::ID = 0;
static RegisterPass<CS201PathProfiling> X("pathProfiling", "CS201PathProfiling Pass", false, false);
