#ifndef __AUFBV_WRAFL_H__
#define __AUFBV_WRAFL_H__

#include <memory>
#include <string>

extern std::string CMD_ARGV0;

struct AUFBVFuzzStat
{
  bool compiled = false;
  bool crashed = false;
  bool timeOut = false;
  bool hasInputVars = false;
  unsigned aflExitCode = 254;
  uint8_t* crashInput = NULL;
};

class AUFBVWrafl
{
 public:
  AUFBVWrafl(std::string target,
        std::string libfile,
        std::string indir,
        std::string outdir,
        unsigned aflTOut);

  // TODO: Implement the following constructor
  // Wrafl(std::string target, std::string indir, std::string outdir, unsigned
  // aflTOut, unsigned testTOut);

  AUFBVFuzzStat fuzz(bool dofuzz);  // default timeout 60s
  AUFBVFuzzStat fuzz(bool dofuzz, unsigned int timeout);

  void cleanup() {}  // cleaning up any temporary files after afl exits
  bool validateCrash(AUFBVFuzzStat const&);
  static bool validatePartialModel(std::string crashInputFile);
  size_t countQueueSize();

  // TODO : validating the input directory
  bool checkSetup(void);
  void disableSeedOpt() { seedopt = false; }

 private:
  // TODO:
  // Collecting interesting inputs from crashes and queue directory of afl
  // output directory
  void collectInterestingInputs(void);
  void collectCrashingInputs(void);

 private:
  std::string srcPath;
  std::string libPath;
  std::string targetPath;
  std::string inputDirPath;
  std::string outputDirPath;
  unsigned int aflTimeout;


  // TODO : use these parameters
  // unsigned int testTimeout;

  // shared pointer reads crash input from file as bytes
  std::string crashInputPath;

  bool seedopt;
};

#endif
