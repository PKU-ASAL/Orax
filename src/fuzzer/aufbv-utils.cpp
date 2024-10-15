#include "aufbv-utils.h"
#include "aufbv-jitgen.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Support/Casting.h"
#include <set>

namespace cvc5 {
namespace cgen {
static void error_value_mapping(llvm::Instruction &I) {
    // print in red
    llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
    I.print(llvm::errs());
    llvm::errs() << "\n";
    assert(false);
}
static void error_unsupported_instruction(llvm::Instruction &I) {
    // print instruction informatin
    // print in red
    llvm::errs() << "\033[31m" << "unsupported instruction: " << "\033[0m\n";
    I.print(llvm::errs());
    llvm::errs() << "\n";
    // print operand information
    llvm::errs() << "operand cnt: " << I.getNumOperands() << "\n";
    for (unsigned i = 0; i < I.getNumOperands(); i++) {
        llvm::errs() << "operand " << i << ": " << I.getOperand(i) << "\n";
        llvm::errs() << "operand " << i << " name: " << I.getOperand(i)->getName() << "\n";
        llvm::errs() << "operand " << i << " type: " << *(I.getOperand(i)->getType()) << "\n";
    }
    assert(false);
}
static llvm::Value* valueMapping(std::map<llvm::Value*, llvm::Value*> *VMap, llvm::Value *val) {
    if (VMap->find(val) == VMap->end()) {
        // is constant
        // constant int
        if (llvm::ConstantInt *CI = llvm::dyn_cast<llvm::ConstantInt>(val)) {
            return llvm::ConstantInt::get(CI->getType(), CI->getZExtValue());
        }
        // constant fp
        if (llvm::ConstantFP *CFP = llvm::dyn_cast<llvm::ConstantFP>(val)) {
            return llvm::ConstantFP::get(CFP->getType(), CFP->getValueAPF().convertToDouble());
        }
        // constant pointer
        if (llvm::ConstantPointerNull *CPN = llvm::dyn_cast<llvm::ConstantPointerNull>(val)) {
            return llvm::ConstantPointerNull::get(llvm::cast<llvm::PointerType>(CPN->getType()));
        }
        #ifdef ENABLE_CBF_DEBUG
        // print in red
        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
        val->print(llvm::errs());
        llvm::errs() << "\n";
        // print val type
        llvm::errs() << "val type: " << *(val->getType()) << "\n";
        // print is constant
        llvm::errs() << "is constant: " << llvm::isa<llvm::Constant>(val) << "\n";
        #endif
        return nullptr;
        return val;
    }
    return (*VMap)[val];
}
static std::string getFunctionName(llvm::Function* F){
    std::string name = F->getName().str();
    if (!isSpecialFunction(name)) {
        return name;
    }
    // check special functions
    for (std::string specialFunctionName : specialFunctions) {
        if (name.find(specialFunctionName) != std::string::npos) {
            return specialFunctionName;
        }
    }
    assert(false);
    return name;
}
static bool copyLLVMFunctionToModuleInternal(llvm::Function *F, llvm::Module *M, std::map<std::string, llvm::Function*> &funcMap){
    // #ifdef ENABLE_CBF_DEBUG
    // llvm::errs() <<
    // "=============================================================\n" <<
    // "copyLLVMFunctionToModule\n" <<
    // "=============================================================\n";
    // // print prompt in cyan
    // llvm::errs() << "\033[36m" << "* Original function:" << "\033[0m\n";
    // F->print(llvm::errs(), nullptr);
    // llvm::errs() << "\033[36m" << "* Original Function type:" << "\033[0m\n";
    // F->getFunctionType()->print(llvm::errs());
    // llvm::errs() << "\n";
    // #endif
    std::string funcName = getFunctionName(F);
    assert(M->getFunction(funcName) != nullptr);
    // create the function in the module
    // llvm::Function *newF = llvm::Function::Create(F->getFunctionType(),
    //                                               llvm::Function::ExternalLinkage,
    //                                               F->getName(),
    //                                               M);
    llvm::Function *newF = M->getFunction(funcName);
    std::map<llvm::Value*, llvm::Value*> VMap;
    // copy the function
    // copy function arguments
    llvm::Function::arg_iterator newArg = newF->arg_begin();
    for (llvm::Argument &Arg : F->args()) {
        newArg->setName(Arg.getName());
        VMap[&Arg] = &*newArg;
        newArg++;
    }
    // copy basic blocks
    for (llvm::BasicBlock &BB : *F) {
        llvm::BasicBlock *newBB = llvm::BasicBlock::Create(M->getContext(),
                                                           BB.getName(),
                                                           newF);
        VMap[&BB] = newBB;
    }
    // IRBuilder
    llvm::IRBuilder<> Builder(M->getContext());
    // copy every instruction
    for (llvm::BasicBlock &BB : *F) {
        bool skip_later = false;
        llvm::BasicBlock *newBB = (llvm::BasicBlock*)valueMapping(&VMap, &BB);
        assert(newBB != nullptr);
        // set builder
        Builder.SetInsertPoint(newBB);
        for (llvm::Instruction &I : BB) {
            if (llvm::isa<llvm::DbgInfoIntrinsic>(I)) {
                continue;
            }
            #ifdef ENABLE_CBF_DEBUG
            // print prompt in cyan
            llvm::errs() << "\033[36m" << "* Original instruction:" << "\033[0m\n";
            I.print(llvm::errs());
            llvm::errs() << "\n";
            llvm::errs() << "\033[36m" << "* Original instruction type:" << "\033[0m\n";
            llvm::errs() << I.getOpcodeName() << "\n";
            #endif
            // copy the instruction
            llvm::Value* newI = nullptr;
            switch(I.getOpcode()) {
                case llvm::Instruction::Ret: {
                    bool isVoidReturn = (I.getNumOperands() == 0);
                    if (isVoidReturn) {
                        newI = Builder.CreateRetVoid();
                    } else {
                        llvm::Value *retVal = valueMapping(&VMap, I.getOperand(0));
                        if (retVal == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newI = Builder.CreateRet(retVal);
                    }
                    break;
                }
                case llvm::Instruction::Br: {
                    llvm::BranchInst *BI = llvm::dyn_cast<llvm::BranchInst>(&I);
                    llvm::BranchInst *newBr;
                    if (BI->isUnconditional()) {
                        llvm::BasicBlock *dest = (llvm::BasicBlock*)valueMapping(&VMap, BI->getOperand(0));
                        if (dest == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newBr = Builder.CreateBr(dest);
                    } else {
                        assert(BI->isConditional() && BI->getNumOperands() == 3);
                        // [Cond, FalseDest,] TrueDest
                        llvm::Value *cond = valueMapping(&VMap, BI->getOperand(0));
                        llvm::BasicBlock *trueDest = (llvm::BasicBlock*)valueMapping(&VMap, BI->getOperand(2));
                        llvm::BasicBlock *falseDest = (llvm::BasicBlock*)valueMapping(&VMap, BI->getOperand(1));
                        if (cond == nullptr || trueDest == nullptr || falseDest == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newBr = Builder.CreateCondBr(cond, trueDest, falseDest);
                    }
                    newI = newBr;
                    break;
                }
                case llvm::Instruction::IndirectBr: {
                    assert(false);
                    llvm::Value *addr = valueMapping(&VMap, I.getOperand(0));
                    if (addr == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::IndirectBrInst *newIBr = Builder.CreateIndirectBr(addr, I.getNumOperands() - 1);
                    for (unsigned i = 1; i < I.getNumOperands(); i++) {
                        llvm::BasicBlock *dest = (llvm::BasicBlock*)valueMapping(&VMap, I.getOperand(i));
                        if (dest == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newIBr->addDestination(dest);
                    }
                    newI = newIBr;
                    break;
                }
                case llvm::Instruction::Switch: {
                    llvm::SwitchInst *SI = llvm::dyn_cast<llvm::SwitchInst>(&I);
                    llvm::Value *cond = valueMapping(&VMap, SI->getCondition());
                    if (cond == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::BasicBlock *defaultDest = (llvm::BasicBlock*)valueMapping(&VMap, SI->getDefaultDest());
                    if (defaultDest == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::SwitchInst *newSwitch = Builder.CreateSwitch(cond, defaultDest, SI->getNumCases());
                    for (llvm::SwitchInst::CaseIt i = SI->case_begin(); i != SI->case_end(); i++) {
                        llvm::BasicBlock *dest = (llvm::BasicBlock*)valueMapping(&VMap, i->getCaseSuccessor());
                        if (dest == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newSwitch->addCase(i->getCaseValue(), dest);
                    }
                    newI = newSwitch;
                    break;
                }
                case llvm::Instruction::Unreachable: {
                    llvm::UnreachableInst *newUnreachable = Builder.CreateUnreachable();
                    newI = newUnreachable;
                    break;
                }
                case llvm::Instruction::Invoke: {
                    // FIXME: returning void is not supported
                    if (I.getType()->isVoidTy()) {
                        assert(false);
                        break;
                    }
                    #ifdef ENABLE_CBF_DEBUG
                    // print in red
                    llvm::errs() << "\033[31m" << "other function call contained: " << "\033[0m\n";
                    I.print(llvm::errs());
                    llvm::errs() << "\n";
                    #endif
                    if (llvm::InvokeInst *II = llvm::dyn_cast<llvm::InvokeInst>(&I)) {
                        llvm::Function *callee = II->getCalledFunction();
                        if (callee == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "Called function is null: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            assert(false);
                            return false;
                        }
                        std::string calleeName = getFunctionName(callee);
                        // check if the function is declared in the module
                        llvm::Function *newCallee = nullptr;
                        assert(M->getFunction(calleeName) != nullptr);
                        assert(funcMap.find(calleeName) != funcMap.end());
                        assert(funcMap[calleeName] == M->getFunction(calleeName));
                        newCallee = funcMap[calleeName];
                        // make new invoke instruction
                        std::vector<llvm::Value*> args;
                        for (unsigned i = 0; i < I.getNumOperands() - 3; i++) {
                            #ifdef ENABLE_CBF_DEBUG
                            llvm::errs() << "operand " << i << ": " << I.getOperand(i) << "\n";
                            llvm::errs() << "operand " << i << " name: " << I.getOperand(i)->getName() << "\n";
                            llvm::errs() << "operand " << i << " type: " << *(I.getOperand(i)->getType()) << "\n";
                            #endif
                            llvm::Value *val = valueMapping(&VMap, I.getOperand(i));
                            if (val == nullptr) {
                                error_value_mapping(I);
                                return false;
                            }
                            args.push_back(val);
                        }
                        llvm::BasicBlock *normalDest = (llvm::BasicBlock*)valueMapping(&VMap, I.getOperand(I.getNumOperands() - 3));
                        llvm::BasicBlock *unwindDest = (llvm::BasicBlock*)valueMapping(&VMap, I.getOperand(I.getNumOperands() - 2));
                        assert(normalDest != nullptr && unwindDest != nullptr);
                        llvm::InvokeInst *newInvoke = Builder.CreateInvoke(newCallee, normalDest, unwindDest, args, "invoke");
                        newI = newInvoke;
                        break;
                    }
                    assert(false);
                    break;
                }
                case llvm::Instruction::Call: {
                    // FIXME: returning void is not supported
                    if (I.getType()->isVoidTy()) {
                        // __cxa_call_unexpected
                        llvm::CallInst *CI = llvm::dyn_cast<llvm::CallInst>(&I);
                        assert(CI != nullptr);
                        llvm::Function *callee = CI->getCalledFunction();
                        assert(callee != nullptr);
                        std::string calleeName = getFunctionName(callee);
                        if (calleeName == "__cxa_call_unexpected") {
                            // handle it
                            llvm::Function *newCallee = M->getFunction(calleeName);
                            assert(newCallee != nullptr);
                            std::vector<llvm::Value*> args;
                            for (unsigned i = 0; i < I.getNumOperands() - 1; i++) {
                                #ifdef ENABLE_CBF_DEBUG
                                llvm::errs() << "operand " << i << ": " << I.getOperand(i) << "\n";
                                llvm::errs() << "operand " << i << " name: " << I.getOperand(i)->getName() << "\n";
                                llvm::errs() << "operand " << i << " type: " << *(I.getOperand(i)->getType()) << "\n";
                                #endif
                                llvm::Value *val = valueMapping(&VMap, I.getOperand(i));
                                if (val == nullptr) {
                                    error_value_mapping(I);
                                    return false;
                                }
                                args.push_back(val);
                            }
                            Builder.CreateCall(newCallee, args);
                            continue;
                        }
                        assert(false);
                        break;
                    }
                    #ifdef ENABLE_CBF_DEBUG
                    // print in red
                    llvm::errs() << "\033[31m" << "other function call contained: " << "\033[0m\n";
                    I.print(llvm::errs());
                    llvm::errs() << "\n";
                    #endif
                    if (llvm::CallInst *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
                        llvm::Function *callee = CI->getCalledFunction();
                        if (callee == nullptr) {
                            error_value_mapping(I);
                            assert(false);
                            return false;
                        }
                        std::string calleeName = getFunctionName(callee);
                        // check if the function is declared in the module
                        llvm::Function *newCallee = nullptr;
                        assert(M->getFunction(calleeName) != nullptr);
                        assert(funcMap.find(calleeName) != funcMap.end());
                        assert(funcMap[calleeName] == M->getFunction(calleeName));
                        newCallee = funcMap[calleeName];
                        // make new call instruction
                        std::vector<llvm::Value*> args;
                        for (unsigned i = 0; i < I.getNumOperands() - 1; i++) {
                            #ifdef ENABLE_CBF_DEBUG
                            llvm::errs() << "operand " << i << ": " << I.getOperand(i) << "\n";
                            llvm::errs() << "operand " << i << " name: " << I.getOperand(i)->getName() << "\n";
                            llvm::errs() << "operand " << i << " type: " << *(I.getOperand(i)->getType()) << "\n";
                            #endif

                            llvm::Value *val = valueMapping(&VMap, I.getOperand(i));
                            if (val == nullptr) {
                                error_value_mapping(I);
                                assert(false);
                                return false;
                            }
                            args.push_back(val);
                        }
                        llvm::CallInst *newCall = Builder.CreateCall(newCallee, args, "call");
                        newI = newCall;
                        break;
                    }
                    assert(false);
                    break;
                }
                case llvm::Instruction::PHI: {
                    llvm::PHINode *newPhi = Builder.CreatePHI(I.getType(), I.getNumOperands() / 2);
                    for (unsigned i = 0; i < I.getNumOperands(); i += 2) {
                        llvm::Value *val = valueMapping(&VMap, I.getOperand(i));
                        llvm::BasicBlock *bb = (llvm::BasicBlock*)valueMapping(&VMap, I.getOperand(i + 1));
                        if (val == nullptr || bb == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newPhi->addIncoming(val, bb);
                    }
                    newI = newPhi;
                    break;
                }
                case llvm::Instruction::Select: {
                    llvm::Value *cond = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *val1 = valueMapping(&VMap, I.getOperand(1));
                    llvm::Value *val2 = valueMapping(&VMap, I.getOperand(2));
                    if (cond == nullptr || val1 == nullptr || val2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newSelect = Builder.CreateSelect(cond, val1, val2);
                    newI = newSelect;
                    break;
                }
                case llvm::Instruction::VAArg: {
                    llvm::VAArgInst *newVAArg = Builder.CreateVAArg(valueMapping(&VMap, I.getOperand(0)), I.getType());
                    if (newVAArg == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    newI = newVAArg;
                    assert(false);
                    break;
                }
                case llvm::Instruction::Add: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newAdd = Builder.CreateAdd(op1, op2, "add");
                    newI = newAdd;
                    break;
                }
                case llvm::Instruction::Sub: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newSub = Builder.CreateSub(op1, op2, "sub");
                    newI = newSub;
                    break;
                }
                case llvm::Instruction::Mul: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newMul = Builder.CreateMul(op1, op2, "mul");
                    newI = newMul;
                    break;
                }
                case llvm::Instruction::UDiv: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newUDiv = Builder.CreateUDiv(op1, op2, "udiv");
                    newI = newUDiv;
                    break;
                }
                case llvm::Instruction::SDiv: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newSDiv = Builder.CreateSDiv(op1, op2, "sdiv");
                    newI = newSDiv;
                    break;
                }
                case llvm::Instruction::URem: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newURem = Builder.CreateURem(op1, op2, "urem");
                    newI = newURem;
                    break;
                }
                case llvm::Instruction::SRem: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newSRem = Builder.CreateSRem(op1, op2, "srem");
                    newI = newSRem;
                    break;
                }
                case llvm::Instruction::And: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newAnd = Builder.CreateAnd(op1, op2, "and");
                    newI = newAnd;
                    break;
                }
                case llvm::Instruction::Or: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newOr = Builder.CreateOr(op1, op2, "or");
                    newI = newOr;
                    break;
                }
                case llvm::Instruction::Xor: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newXor = Builder.CreateXor(op1, op2, "xor");
                    newI = newXor;
                    break;
                }
                case llvm::Instruction::Shl: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newShl = Builder.CreateShl(op1, op2, "shl");
                    newI = newShl;
                    break;
                }
                case llvm::Instruction::LShr: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newLShr = Builder.CreateLShr(op1, op2, "lshr");
                    newI = newLShr;
                    break;
                }
                case llvm::Instruction::AShr: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newAShr = Builder.CreateAShr(op1, op2, "ashr");
                    newI = newAShr;
                    break;
                }
                case llvm::Instruction::ICmp: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::ICmpInst *ci = llvm::dyn_cast<llvm::ICmpInst>(&I);
                    llvm::CmpInst::Predicate pred = ci->getPredicate();
                    llvm::Value *newCmp = Builder.CreateICmp(pred, op1, op2, "icmp");
                    newI = newCmp;
                    break;
                }
                case llvm::Instruction::Alloca: {
                    #ifdef ENABLE_LLVM11
                    llvm::AllocaInst *newAlloca = Builder.CreateAlloca(I.getType()->getPointerElementType(), nullptr, "alloca");
                    #else
                    llvm::AllocaInst *newAlloca = Builder.CreateAlloca(I.getType(), nullptr, "alloca");
                    #endif
                    // copy all the args
                    for (unsigned i = 0; i < I.getNumOperands(); i++) {
                        llvm::Value *val = valueMapping(&VMap, I.getOperand(i));
                        if (val == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                        newAlloca->setOperand(i, val);
                    }
                    newI = newAlloca;
                    break;
                }
                case llvm::Instruction::Load: {
                    llvm::Value *addr = valueMapping(&VMap, I.getOperand(0));
                    if (addr == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    auto elementType = I.getType();
                    if (addr->getType() != elementType->getPointerTo()) {
                        // bitcast addr to elementType pointer type
                        llvm::Value *newAddr = Builder.CreateBitCast(addr, elementType->getPointerTo(), "bitcast");
                        addr = newAddr;
                    }
                    #ifdef ENABLE_LLVM11
                    llvm::LoadInst *newLoad = Builder.CreateLoad(elementType, addr, "load");
                    #else
                    llvm::Value *newLoad = Builder.CreateLoad(elementType, addr, "load");
                    #endif
                    newI = newLoad;
                    break;
                }
                case llvm::Instruction::Store: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *addr = valueMapping(&VMap, I.getOperand(1));
                    if (val == nullptr || addr == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    // bitcast addr to val pointer type
                    if (val->getType() != addr->getType()->getPointerElementType()) {
                        llvm::Value *newAddr = Builder.CreateBitCast(addr, val->getType()->getPointerTo(), "bitcast");
                        llvm::StoreInst *newStore = Builder.CreateStore(val, newAddr, "store");
                        newI = newStore;
                        break;
                    }
                    llvm::StoreInst *newStore = Builder.CreateStore(val, addr, "store");
                    newI = newStore;
                    break;
                }
                case llvm::Instruction::GetElementPtr: {
                    llvm::Value *ptr = valueMapping(&VMap, I.getOperand(0));
                    if (ptr == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    // indices
                    std::vector<llvm::Value*> indices;
                    for (unsigned i = 1; i < I.getNumOperands(); i++) {
                        indices.push_back(valueMapping(&VMap, I.getOperand(i)));
                        if (indices.back() == nullptr) {
                            #ifdef ENABLE_CBF_DEBUG
                            // print in red
                            llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                            I.print(llvm::errs());
                            llvm::errs() << "\n";
                            #endif
                            return false;
                        }
                    }
                    #ifdef ENABLE_LLVM11
                    llvm::Value *newGEP = Builder.CreateGEP(ptr, indices, "gep");
                    #else
                    llvm::Value *newGEP = Builder.CreateGEP(ptr->getType()->getPointerElementType(), ptr, indices, "gep");
                    #endif
                    newI = newGEP;
                    break;
                }
                case llvm::Instruction::Trunc: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newTrunc = Builder.CreateTrunc(val, I.getType(), "trunc");
                    newI = newTrunc;
                    break;
                }
                case llvm::Instruction::ZExt: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newZExt = Builder.CreateZExt(val, I.getType(), "zext");
                    newI = newZExt;
                    break;
                }
                case llvm::Instruction::SExt: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newSExt = Builder.CreateSExt(val, I.getType(), "sext");
                    newI = newSExt;
                    break;
                }
                case llvm::Instruction::IntToPtr: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newIntToPtr = Builder.CreateIntToPtr(val, I.getType(), "inttoptr");
                    newI = newIntToPtr;
                    break;
                }
                case llvm::Instruction::PtrToInt: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newPtrToInt = Builder.CreatePtrToInt(val, I.getType(), "ptrtoint");
                    newI = newPtrToInt;
                    break;
                }
                case llvm::Instruction::BitCast: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newBitCast = Builder.CreateBitCast(val, I.getType(), "bitcast");
                    newI = newBitCast;
                    break;
                }
                case llvm::Instruction::FNeg: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFNeg = Builder.CreateFNeg(val, "fneg");
                    newI = newFNeg;
                    break;
                }
                case llvm::Instruction::FAdd: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFAdd = Builder.CreateFAdd(op1, op2, "fadd");
                    newI = newFAdd;
                    break;
                }
                case llvm::Instruction::FSub: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFSub = Builder.CreateFSub(op1, op2, "fsub");
                    newI = newFSub;
                    break;
                }
                case llvm::Instruction::FMul: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFMul = Builder.CreateFMul(op1, op2, "fmul");
                    newI = newFMul;
                    break;
                }
                case llvm::Instruction::FDiv: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFDiv = Builder.CreateFDiv(op1, op2, "fdiv");
                    newI = newFDiv;
                    break;
                }
                case llvm::Instruction::FRem: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFRem = Builder.CreateFRem(op1, op2, "frem");
                    newI = newFRem;
                    break;
                }
                case llvm::Instruction::FPTrunc: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFPTrunc = Builder.CreateFPTrunc(val, I.getType(), "fptrunc");
                    newI = newFPTrunc;
                    break;
                }
                case llvm::Instruction::FPExt: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFPExt = Builder.CreateFPExt(val, I.getType(), "fpext");
                    newI = newFPExt;
                    break;
                }
                case llvm::Instruction::FPToUI: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFPToUI = Builder.CreateFPToUI(val, I.getType(), "fptoui");
                    newI = newFPToUI;
                    break;
                }
                case llvm::Instruction::FPToSI: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newFPToSI = Builder.CreateFPToSI(val, I.getType(), "fptosi");
                    newI = newFPToSI;
                    break;
                }
                case llvm::Instruction::UIToFP: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newUIToFP = Builder.CreateUIToFP(val, I.getType(), "uitofp");
                    newI = newUIToFP;
                    break;
                }
                case llvm::Instruction::SIToFP: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newSIToFP = Builder.CreateSIToFP(val, I.getType(), "sitofp");
                    newI = newSIToFP;
                    break;
                }
                case llvm::Instruction::FCmp: {
                    llvm::Value *op1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *op2 = valueMapping(&VMap, I.getOperand(1));
                    if (op1 == nullptr || op2 == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::FCmpInst *ci = llvm::dyn_cast<llvm::FCmpInst>(&I);
                    llvm::CmpInst::Predicate pred = ci->getPredicate();
                    llvm::Value *newCmp = Builder.CreateFCmp(pred, op1, op2, "fcmp");
                    newI = newCmp;
                    break;
                }
                case llvm::Instruction::InsertValue: {
                    llvm::InsertValueInst *oldInsertValue = llvm::dyn_cast<llvm::InsertValueInst>(&I);
                    llvm::Value *val = valueMapping(&VMap, oldInsertValue->getAggregateOperand());
                    llvm::Value *elem = valueMapping(&VMap, oldInsertValue->getInsertedValueOperand());
                    if (val == nullptr || elem == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    // indices
                    std::vector<unsigned> indices;
                    for (unsigned i = 0; i < oldInsertValue->getNumIndices(); i++) {
                        indices.push_back(oldInsertValue->getIndices()[i]);
                    }
                    llvm::Value *newInsertValue = Builder.CreateInsertValue(val, elem, indices, "insertvalue");
                    newI = newInsertValue;
                    break;
                }
                case llvm::Instruction::ExtractValue: {
                    llvm::ExtractValueInst *oldExtractValue = llvm::dyn_cast<llvm::ExtractValueInst>(&I);
                    llvm::Value *val = valueMapping(&VMap, oldExtractValue->getAggregateOperand());
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    // indices
                    std::vector<unsigned> indices;
                    for (unsigned i = 0; i < oldExtractValue->getNumIndices(); i++) {
                        indices.push_back(oldExtractValue->getIndices()[i]);
                    }
                    llvm::Value *newExtractValue = Builder.CreateExtractValue(val, indices, "extractvalue");
                    newI = newExtractValue;
                    break;
                }
                case llvm::Instruction::Fence: {
                    assert(false);
                    break;
                }
                case llvm::Instruction::InsertElement: {
                    llvm::Value *vec = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *elem = valueMapping(&VMap, I.getOperand(1));
                    llvm::Value *idx = valueMapping(&VMap, I.getOperand(2));
                    if (vec == nullptr || elem == nullptr || idx == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newInsertElement = Builder.CreateInsertElement(vec, elem, idx, "insertelement");
                    newI = newInsertElement;
                    break;
                }
                case llvm::Instruction::ExtractElement: {
                    llvm::Value *vec = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *idx = valueMapping(&VMap, I.getOperand(1));
                    if (vec == nullptr || idx == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newExtractElement = Builder.CreateExtractElement(vec, idx, "extractelement");
                    newI = newExtractElement;
                    break;
                }
                case llvm::Instruction::ShuffleVector: {
                    llvm::Value *vec1 = valueMapping(&VMap, I.getOperand(0));
                    llvm::Value *vec2 = valueMapping(&VMap, I.getOperand(1));
                    llvm::Value *mask = valueMapping(&VMap, I.getOperand(2));
                    if (vec1 == nullptr || vec2 == nullptr || mask == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newShuffleVector = Builder.CreateShuffleVector(vec1, vec2, mask, "shufflevector");
                    newI = newShuffleVector;
                    break;
                }
                case llvm::Instruction::Resume: {
                    llvm::Value *val = valueMapping(&VMap, I.getOperand(0));
                    if (val == nullptr) {
                        #ifdef ENABLE_CBF_DEBUG
                        // print in red
                        llvm::errs() << "\033[31m" << "value Mapping error: " << "\033[0m\n";
                        I.print(llvm::errs());
                        llvm::errs() << "\n";
                        #endif
                        return false;
                    }
                    llvm::Value *newResume = Builder.CreateResume(val);
                    newI = newResume;
                    break;
                }
                case llvm::Instruction::LandingPad: {
                    llvm::LandingPadInst * oldLandingPad = llvm::dyn_cast<llvm::LandingPadInst>(&I);
                    auto *newLandingPad = Builder.CreateLandingPad(oldLandingPad->getType(), oldLandingPad->getNumClauses(), "landingpad");
                    for (unsigned i = 0; i < oldLandingPad->getNumClauses(); i++) {
                        auto clause = oldLandingPad->getClause(i);
                        // assert clause is constant
                        assert(llvm::isa<llvm::Constant>(clause));
                        // create a new constant in the new function
                        if (llvm::isa<llvm::ConstantInt>(clause)) {
                            llvm::ConstantInt *oldClause = llvm::dyn_cast<llvm::ConstantInt>(clause);
                            llvm::Constant *newClause = llvm::ConstantInt::get(oldClause->getType(), oldClause->getZExtValue());
                            newLandingPad->addClause(newClause);
                            continue;
                        }
                        if (llvm::isa<llvm::ConstantFP>(clause)) {
                            llvm::ConstantFP *oldClause = llvm::dyn_cast<llvm::ConstantFP>(clause);
                            llvm::Constant *newClause = llvm::ConstantFP::get(oldClause->getType(), oldClause->getValueAPF());
                            newLandingPad->addClause(newClause);
                            continue;
                        }
                        if (llvm::isa<llvm::ConstantPointerNull>(clause)) {
                            llvm::ConstantPointerNull *oldClause = llvm::dyn_cast<llvm::ConstantPointerNull>(clause);
                            llvm::Constant *newClause = llvm::ConstantPointerNull::get(llvm::dyn_cast<llvm::PointerType>(oldClause->getType()));
                            newLandingPad->addClause(newClause);
                            continue;
                        }
                        if (llvm::isa<llvm::ConstantAggregateZero>(clause)) {
                            llvm::ConstantAggregateZero *oldClause = llvm::dyn_cast<llvm::ConstantAggregateZero>(clause);
                            llvm::Constant *newClause = llvm::ConstantAggregateZero::get(oldClause->getType());
                            newLandingPad->addClause(newClause);
                            continue;
                        }
                        assert(false);
                    }
                    newI = newLandingPad;
                    break;
                }
                case llvm::Instruction::AtomicRMW: {
                    error_unsupported_instruction(I);
                    assert(false);
                    break;
                }
                case llvm::Instruction::AtomicCmpXchg: {
                    error_unsupported_instruction(I);
                    assert(false);
                    break;
                }
                default: {
                    error_unsupported_instruction(I);
                    assert(false);
                    break;
                }
            }
            if (skip_later) {
                // add unreachable
                llvm::UnreachableInst *newUnreachable = Builder.CreateUnreachable();
                newI = newUnreachable;
                break;
            }
            if (newI == nullptr) {
                #ifdef ENABLE_CBF_DEBUG
                // print in red
                llvm::errs() << "\033[31m" << "new instruction is null: " << "\033[0m\n";
                I.print(llvm::errs());
                llvm::errs() << "\n";
                #endif
                assert(false);
            }
            // insert the instruction
            VMap[&I] = newI;
        }
    }
    #ifdef ENABLE_CBF_DEBUG
    // newF->print(llvm::errs(), nullptr);
    #endif
    // // set function attributes: "no-jump-tables"="false"
    // llvm::AttrBuilder attrBuilder;
    // attrBuilder.addAttribute("no-jump-tables", "false");
    // newF->setAttributes(llvm::AttributeList::get(newF->getContext(), llvm::AttributeList::FunctionIndex, attrBuilder));
    // print function attributes
    #ifdef ENABLE_CBF_DEBUG
    // llvm::errs() << "\033[36m" << "* Function attributes:" << "\033[0m\n";
    // F->getAttributes().dump();
    // llvm::errs() << "\033[36m" << "* New Function attributes:" << "\033[0m\n";
    // newF->getAttributes().dump();
    // llvm::errs() << "\n";
    #endif
    // FIXME: function verification
    // if (llvm::verifyFunction(*newF, &llvm::errs())){
    //     #ifdef ENABLE_CBF_DEBUG
    //     llvm::errs() << "\033[31m" << "Function verification failed." << "\033[0m\n";
    //     #endif
    //     assert(false);
    // }
    llvm::verifyFunction(*newF, &llvm::errs());
    // DEBUG: print the function
    #ifdef ENABLE_CBF_DEBUG
    // llvm::errs() << "\033[36m" << "* New function:" << "\033[0m\n";
    // newF->print(llvm::errs(), nullptr);
    // function verification
    // funcMap[F->getName().str()] = newF;
    // print function type
    // llvm::errs() << "\033[36m" << "* New Function type:" << "\033[0m\n";
    // newF->getFunctionType()->print(llvm::errs());
    // llvm::errs() << "\n";
    #endif
    return true;
}
static bool declareRelatedFunctionsInOrder(llvm::Function *F, llvm::Module *M, std::vector<llvm::Function*> &unhandledFunctionsInOrder, std::map<std::string, llvm::Function*> &funcMap) {
    assert(unhandledFunctionsInOrder.size() == 0);
    assert(funcMap.size() == 0);
    std::set<std::string> visitedFunctionNames;
    std::map<llvm::Function*, std::vector<llvm::Function*>> callGraph;
    std::set<llvm::Function*> unhandledDeclarations;
    unhandledDeclarations.insert(F);
    while (!unhandledDeclarations.empty()) {
        llvm::Function *curF = *unhandledDeclarations.begin();
        unhandledDeclarations.erase(unhandledDeclarations.begin());
        std::string funcName = getFunctionName(curF);
        // if the function has been handled, skip it
        if (visitedFunctionNames.find(funcName) != visitedFunctionNames.end()) {
            continue;
        }
        visitedFunctionNames.insert(funcName);
        // if it is just declaration, check if it is special function
        if (isSpecialFunction(funcName)) {
            continue;
        }
        #ifdef ENABLE_CBF_DEBUG
        llvm::errs() << "curF: " << funcName << "\n";
        #endif
        // assert(!curF->isDeclaration());
        if (callGraph.find(curF) == callGraph.end()) {
            callGraph[curF] = std::vector<llvm::Function*>();
        }
        if (curF->isDeclaration()) {
            continue;
        }
        // find more functions to declare
        for (llvm::Function::iterator BB = curF->begin(), FE = curF->end(); BB != FE; ++BB) {
            for (llvm::BasicBlock::iterator I = BB->begin(), E = BB->end(); I != E; ++I) {
                llvm::Instruction &inst = *I;
                if (llvm::isa<llvm::DbgInfoIntrinsic>(inst)) {
                    continue;
                }
                if (inst.getOpcode() == llvm::Instruction::Call) {
                    llvm::CallInst *ci = llvm::dyn_cast<llvm::CallInst>(&inst);
                    llvm::Function *callee = ci->getCalledFunction();
                    if (callee == nullptr) {
                        assert(false);
                        continue;
                    }
                    std::string calleeName = getFunctionName(callee);
                    if (visitedFunctionNames.find(calleeName) != visitedFunctionNames.end()) {
                        continue;
                    }
                    unhandledDeclarations.insert(callee);
                    // add edge
                    assert(callGraph.find(curF) != callGraph.end());
                    callGraph[curF].push_back(callee);
                }
                else if (inst.getOpcode() == llvm::Instruction::Invoke) {
                    llvm::InvokeInst *ii = llvm::dyn_cast<llvm::InvokeInst>(&inst);
                    if (ii->getType()->isVoidTy()) {
                        assert(false);
                        continue;
                    }
                    llvm::Function *callee = ii->getCalledFunction();
                    if (callee == nullptr) {
                        assert(false);
                        continue;
                    }
                    std::string calleeName = getFunctionName(callee);
                    if (visitedFunctionNames.find(calleeName) != visitedFunctionNames.end()) {
                        continue;
                    }
                    unhandledDeclarations.insert(callee);
                    // add edge
                    assert(callGraph.find(curF) != callGraph.end());
                    callGraph[curF].push_back(callee);
                }
            }
        }
    }
    // reverse topological sort callGraph, and add result to unhandledFunctionsInOrder
    // edge: v -> w, w is a precondition of v
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "\033[36m" << "* callGraph:" << "\033[0m\n";
    for (auto it = callGraph.begin(); it != callGraph.end(); it++) {
        llvm::errs() << getFunctionName(it->first) << " -> ";
        for (auto it2 = it->second.begin(); it2 != it->second.end(); it2++) {
            llvm::errs() << getFunctionName(*it2) << " ";
        }
        llvm::errs() << "\n";
    }
    #endif
    reverse_topsort(callGraph, unhandledFunctionsInOrder);
    if (unhandledFunctionsInOrder.size() != visitedFunctionNames.size()){
        #ifdef ENABLE_CBF_DEBUG
        llvm::errs() << "unhandledFunctionsInOrder.size() != visitedFunctionNames.size(): " << unhandledFunctionsInOrder.size() << " " << visitedFunctionNames.size() << "\n";
        // print unhandledFunctionsInOrder
        for (auto it = unhandledFunctionsInOrder.begin(); it != unhandledFunctionsInOrder.end(); it++) {
            llvm::errs() << getFunctionName(*it) << " ";
        }
        llvm::errs() << "\n";
        // print visitedFunctionNames
        for (auto it = visitedFunctionNames.begin(); it != visitedFunctionNames.end(); it++) {
            llvm::errs() << *it << " ";
        }
        llvm::errs() << "\n";
        #endif
        assert(false);
    }
    // add to funcMap
    for (auto it = unhandledFunctionsInOrder.begin(); it != unhandledFunctionsInOrder.end(); it++) {
        llvm::Function *curF = *it;
        std::string funcName = getFunctionName(curF);
        // only declare the function in module M
        llvm::Function *newF = llvm::Function::Create(curF->getFunctionType(), llvm::Function::ExternalLinkage, funcName, M);
        funcMap[funcName] = newF;
    }
    assert(funcMap.size() == visitedFunctionNames.size());
    return true;
}

bool copyLLVMFunctionToModule(llvm::Function *F, llvm::Module *M){
    std::vector<llvm::Function*> unhandledFunctionsInOrder;
    std::set<std::string> handledFunctionNames;
    std::map<std::string, llvm::Function*> funcMap;
    handledFunctionNames.clear();
    if (!declareRelatedFunctionsInOrder(F, M, unhandledFunctionsInOrder, funcMap)) {
        assert(false);
        return false;
    }
    // print func Map
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "\033[36m" << "* Function Map:" << "\033[0m\n";
    for (auto it = funcMap.begin(); it != funcMap.end(); it++) {
        llvm::errs() << it->first << " -> " << it->second->getName().str() << "\n";
    }
    #endif
    size_t handled_threshold = 10;
    for (auto it = unhandledFunctionsInOrder.begin(); it != unhandledFunctionsInOrder.end(); it++) {
        llvm::Function *curF = *it;
        // if the function has been handled, skip it
        std::string funcName = getFunctionName(curF);
        if (handledFunctionNames.find(funcName) != handledFunctionNames.end()) {
            continue;
        }
        if (handledFunctionNames.size() > handled_threshold) {
            #ifdef ENABLE_CBF_DEBUG
            llvm::errs() << "copyLLVMFunctionToModule: threshold reached\n";
            #endif
            assert(false);
        }
        // handle special function in switch
        // copy the function
        // if the function has been registered, skip it
        if (cvc5::cgen::JITFunctionNames.find(funcName) == cvc5::cgen::JITFunctionNames.end()) {
            if (!curF->isDeclaration()) {
                // declare personality function if needed
                if (curF->hasPersonalityFn()) {
                    llvm::Constant *personalityFn = curF->getPersonalityFn();
                    assert(funcMap.find(funcName) != funcMap.end());
                    llvm::Function *newF = funcMap[funcName];
                    newF->setPersonalityFn(personalityFn);
                }
                if (!copyLLVMFunctionToModuleInternal(curF, M, funcMap)) {
                    assert(false);
                    return false;
                }
                cvc5::cgen::JITFunctionNames.insert(funcName);
            }
        }
        handledFunctionNames.insert(funcName);
    }
    #ifdef ENABLE_CBF_DEBUG
    // print the module
    llvm::errs() << "\033[36m" << "* New Module:" << "\033[0m\n";
    M->print(llvm::errs(), nullptr);
    #endif
    // assert(false);
    return true;
}
}
}