#ifndef __AUFBV_JIT__
#define __AUFBV_JIT__

#include "llvm/ADT/StringRef.h"
#include "llvm/ExecutionEngine/JITSymbol.h"
#include "llvm/ExecutionEngine/Orc/CompileUtils.h"
#include "llvm/ExecutionEngine/Orc/Core.h"
#include "llvm/ExecutionEngine/Orc/ExecutionUtils.h"
#include "llvm/ExecutionEngine/Orc/IRCompileLayer.h"
#include "llvm/ExecutionEngine/Orc/JITTargetMachineBuilder.h"
#include "llvm/ExecutionEngine/Orc/RTDyldObjectLinkingLayer.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/LLVMContext.h"
#include <memory>
#include <string>

namespace llvm {
namespace orc {

class AUFBVJIT {
private:
  ExecutionSession ES;
  RTDyldObjectLinkingLayer ObjectLayer;
  IRCompileLayer CompileLayer;

  DataLayout DL;
  MangleAndInterner Mangle;
  ThreadSafeContext Ctx;

  JITDylib &MainJD;

public:
  AUFBVJIT(JITTargetMachineBuilder JTMB, DataLayout DL)
      : ObjectLayer(ES,
                    []() { return std::make_unique<SectionMemoryManager>(); }),
        CompileLayer(ES, ObjectLayer,
                     std::make_unique<ConcurrentIRCompiler>(std::move(JTMB))),
        DL(std::move(DL)), Mangle(ES, this->DL),
        Ctx(std::make_unique<LLVMContext>()),
        MainJD(ES.createBareJITDylib("<main>")) {
    MainJD.addGenerator(
        cantFail(DynamicLibrarySearchGenerator::GetForCurrentProcess(
            DL.getGlobalPrefix())));
  }

  static Expected<std::unique_ptr<AUFBVJIT>> Create() {
    auto JTMB = JITTargetMachineBuilder::detectHost();

    if (!JTMB)
      return JTMB.takeError();

    auto DL = JTMB->getDefaultDataLayoutForTarget();
    if (!DL)
      return DL.takeError();

    return std::make_unique<AUFBVJIT>(std::move(*JTMB), std::move(*DL));
  }

  const DataLayout &getDataLayout() const { return DL; }

  LLVMContext &getContext() { return *Ctx.getContext(); }

  Error addModule(std::unique_ptr<Module> M) {
    return CompileLayer.add(MainJD, ThreadSafeModule(std::move(M), Ctx));
  }

  Error removeTargets(size_t targetCnt) {
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "\033[36m" << "* Remove targets from module:\n" << "\033[0m";
    #endif
    llvm::orc::SymbolNameSet targetNames;
    std::string targetName = "targetFunction";
    for (size_t i = 0; i < targetCnt; i++) {
      std::string funcname = targetName + std::to_string(i);
      targetNames.insert(Mangle(funcname));
      #ifdef ENABLE_CBF_DEBUG
      llvm::errs() << funcname << " removed.\n";
      #endif
    }
    if (auto Err = MainJD.remove(targetNames))
      return Err;
    return Error::success();
  }

  Error removeSymbols(std::vector<std::string> &symbols) {
    llvm::orc::SymbolNameSet targetNames;
    for (auto &symbol : symbols) {
      #ifdef ENABLE_CBF_DEBUG
      llvm::errs() << "Removing symbol: " << symbol << "\n";
      #endif
      targetNames.insert(Mangle(symbol));
    }
    if (auto Err = MainJD.remove(targetNames))
      return Err;
    return Error::success();
  }

  Expected<JITEvaluatedSymbol> lookup(StringRef Name) {
    #ifdef ENABLE_CBF_DEBUG
    llvm::errs() << "lookup: " << Name << "\n";
    #endif
    return ES.lookup({&MainJD}, Mangle(Name.str()));
  }
};

} // end namespace orc
} // end namespace llvm

#endif