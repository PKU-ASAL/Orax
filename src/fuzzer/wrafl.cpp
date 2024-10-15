
#include "wrafl.h"

#include <unistd.h>

#include <boost/filesystem.hpp>
#include <boost/lambda/bind.hpp>
#include <boost/process.hpp>
#include <boost/throw_exception.hpp>
#include <boost/process/environment.hpp>

#include <cstdio>
#include <iostream>
#include <set>
#include <termcolor.hpp>

#include <chrono>
#include <unistd.h>

using namespace std;


namespace bfs = boost::filesystem;
namespace bp = boost::process;

Wrafl::Wrafl(std::string srcfile,
             std::string libfile,
             std::string indir,
             std::string outdir,
             unsigned aflTOut)
    : srcPath(srcfile),
      libPath(libfile),
      targetPath("./a.out"),
      inputDirPath(indir),
      outputDirPath(outdir),
      aflTimeout(aflTOut),
      crashInputPath(), seedopt(true) {}

bool Wrafl::checkSetup(void)
{
  if (access(AFL_BIN_PATH, F_OK))
  {
    std::cout << "AFL Binary not found.\n";
    return false;
  }

  if (!bfs::is_directory(inputDirPath)) {
    if (bfs::is_empty(inputDirPath)) {
      BOOST_THROW_EXCEPTION(std::runtime_error("Seed input directory not found or empty. Exiting...\n"));
      exit(1);
    }
  }

  if (!bfs::exists(srcPath))
  {
    return false;
  }
  else
  {
    std::string aflcc = AFL_CC_PATH;
    // boost::filesystem::path hgfuzzCC = HGFUZZ_CC_PATH;
    // std::string includeDir = "-I" + std::string(HGFUZZ_PATH);
    int compiled = 1;
    auto aflcc_env {boost::this_process::environment()};
    aflcc_env["AFL_LLVM_CMPLOG"]= "1";
    aflcc_env["AFL_LLVM_LAF_TRANSFORM_COMPARES"]= "1";
    aflcc_env["AFL_LLVM_LAF_SPLIT_COMPARES"]= "1";
    std::cout << termcolor::blue;
    if (libPath.size())
      compiled = bp::system(aflcc, srcPath, libPath, aflcc_env, bp::std_out > "aflcc_log.txt"
			    , bp::std_err > bp::null);

    std::cout << "afl-clang-fast compilation : ";

    if (compiled)
    {
      std::cout << "[FAILED]" << termcolor::reset << std::endl;
      return false;
    }
    else
    {
      std::cout << "[OK]" << std::endl;
    }
  }

  if (!bfs::exists(inputDirPath))
  {
    std::cout << "Input directory doesn't exit\n" << termcolor::reset;
    return false;
  }

  if (bfs::is_empty(inputDirPath))
  {
    std::cout << "Input directory doesn't have any seed inputs\nExiting...\n"
              << termcolor::reset;
    return false;
  }

  return true;
}

// TODO: don't exit from wrafl, return proper error codes
// FuzzStat Wrafl::fuzz(bool dofuzz, unsigned int timeout)
// {
//   FuzzStat fuzzStat;
//   if (!checkSetup())
//   {
//     fuzzStat.compiled = false;
//     return fuzzStat;
//   }

//   FILE* aflFuzzOut = fopen("afl_fuzz.log", "w");

//   if (dofuzz)
//   {
//     // TODO : should this be here or make it a class variable
//     std::string aflFuzzBin = AFL_BIN_PATH;
//     std::string launchCommand = aflFuzzBin + " -D -i " + inputDirPath + " -o "
//                                 + outputDirPath + " " + targetPath;

//     auto aflfuzz_env {boost::this_process::environment()};
//     aflfuzz_env["AFL_NO_UI"] = "1"; // do not show afl status screen
//     aflfuzz_env["AFL_BENCH_UNTIL_CRASH"] = "1";
//     aflfuzz_env["AFL_NO_AFFINITY"] = "1";
//     std::cout << termcolor::blue;
//     std::cout << "AFL command : " << launchCommand << std::endl;
//     // bp::child aflFuzzMain(launchCommand, aflfuzz_env, bp::std_out > bp::null);
//     auto start = chrono::steady_clock::now();
//     bp::child aflFuzzMain(launchCommand, aflfuzz_env, bp::std_out > aflFuzzOut, bp::std_err > aflFuzzOut);

//     if (!aflFuzzMain.wait_for(std::chrono::seconds(timeout)))
//     {
//       fuzzStat.timeOut = true;
//       aflFuzzMain.terminate();
//     }

//     aflFuzzMain.wait();

//     auto stop = chrono::steady_clock::now();
//     std::cout << "TIME taken: " << chrono::duration_cast<chrono::milliseconds>(stop - start).count() << "sec" << std::endl;

//     std::cout << "AFL-Fuzz main exit code : " << aflFuzzMain.exit_code() << std::endl;
//     fuzzStat.aflExitCode = aflFuzzMain.exit_code();
//     std::cout << "AFL-Fuzz timed out : ";

//     if (fuzzStat.timeOut) {
//       std::cout << "YES\n";
//       fuzzStat.crashed = false;
//       fuzzStat.timeOut = true;
//     }
//     else {
//       std::cout << "NO\n";
//       fuzzStat.crashed = true;
//       fuzzStat.timeOut = false;


//       if(aflFuzzMain.exit_code() == 1) {
//         std::cout << "Checking for possible crashing seed input..." << std::endl;
//         bfs::path inDir(inputDirPath);
//         for (bfs::directory_entry& item : bfs::directory_iterator(inDir)) {
//           if (bfs::is_regular(item)) {
//             FILE* fp = std::fopen(item.path().string().c_str(), "rb");
//             std::cout << "input file path: " << item.path() << std::endl;

//             bp::child target(targetPath,
//                              bp::std_in = fp,
//                              bp::std_out > bp::null, bp::std_err > bp::null);
//             target.wait();
//             fclose(fp);
//             if (target.exit_code() == SIGABRT) {
//               std::cout << "CRASHED FOR : " << item.path() << std::endl;
//               fuzzStat.aflExitCode = 0;
//               break;
//             }
//           }
//         }
//       }
//       else if(seedopt)
// 	collectInterestingInputs();


//       else {
//         BOOST_THROW_EXCEPTION(std::runtime_error("Unknown issue with afl-fuzz"));
//         exit(1);
//       }
//     }

//     std::cout << "AFL-Fuzz exiting. " << std::endl;
//   }
//   else
//   {
//     std::cout << "Dry running without fuzz loop" << std::endl;
//     bp::child targetProg(targetPath /*, bp::std_out = aflFuzzOut */);
//     targetProg.wait();
//     fuzzStat.aflExitCode = targetProg.exit_code();
//     if (targetProg.exit_code() == SIGABRT) {
//       fuzzStat.crashed = true;
//       fuzzStat.timeOut = false;

//     }

//     fuzzStat.hasInputVars = false;
//   }

//   fclose(aflFuzzOut);

//   std::cout << std::endl << termcolor::reset;
//   return fuzzStat;
// }

FuzzStat Wrafl::fuzz(bool dofuzz, unsigned int timeout)
{
  FuzzStat fuzzStat;
  // orax
  FILE* fsolver_out = fopen("fsolver.log", "w");
  FILE* compile_test_out = fopen("compile_test.log", "w");
  if (dofuzz)
  {
    // orax
    // TODO: should this be here or make it a class variable
    std::string fsolver_path = "TODO: fsolver path";
    auto start = chrono::steady_clock::now();

    // compile dlib: TODO: debug
    std::string compileTestCommand = "clang -shared target.c -o target.so";
    std::cout << termcolor::blue;
    std::cout << "Compile Test command : " << compileTestCommand << std::endl;
    auto compile_test_env {boost::this_process::environment()};
    bp::child compile_test(compileTestCommand, compile_test_env, bp::std_out > compile_test_out, bp::std_err > compile_test_out);
    if (!compile_test.wait_for(std::chrono::seconds(timeout)))
    {
      fuzzStat.timeOut = true;
      compile_test.terminate();
    }
    compile_test.wait();

    // launch fsolver
    std::string launchCommand = fsolver_path + " -l ./target.so";
    auto fsolver_env {boost::this_process::environment()};
    std::cout << termcolor::blue;
    std::cout << "Fsolver command : " << launchCommand << std::endl;
    bp::child fsolver_main(launchCommand, fsolver_env, bp::std_out > fsolver_out, bp::std_err > fsolver_out);
    if (!fsolver_main.wait_for(std::chrono::seconds(timeout)))
    {
      fuzzStat.timeOut = true;
      fsolver_main.terminate();
    }
    fsolver_main.wait();

    auto stop = chrono::steady_clock::now();
    std::cout << "TIME taken: " << chrono::duration_cast<chrono::milliseconds>(stop - start).count() << "sec" << std::endl;

    std::cout << "fsolver main exit code : " << fsolver_main.exit_code() << std::endl;
    fuzzStat.aflExitCode = fsolver_main.exit_code();
    std::cout << "fsolver_main timed out : ";

    if (fuzzStat.timeOut) {
      std::cout << "YES\n";
      fuzzStat.crashed = false;
      fuzzStat.timeOut = true;
    }
    else {
      std::cout << "NO\n";
      fuzzStat.crashed = false;
      fuzzStat.timeOut = false;

      std::cout << "Checking for possible crashing seed input..." << std::endl;
      std::ifstream in("solution.txt");
      std::string line;
      if (in){
        while (getline(in, line)){
          if (line.find("sat") != string::npos){
            std::cout << "SAT!" << std::endl;
            fuzzStat.crashed = true;
            break;
          }
        }
      }
      else{
        std::cout << "No solution.txt file found" << std::endl;
      }
      // if(fsolver_main.exit_code() == 1) {
      //   std::cout << "Checking for possible crashing seed input..." << std::endl;
      //   bfs::path inDir(inputDirPath);
      //   for (bfs::directory_entry& item : bfs::directory_iterator(inDir)) {
      //     if (bfs::is_regular(item)) {
      //       FILE* fp = std::fopen(item.path().string().c_str(), "rb");
      //       std::cout << "input file path: " << item.path() << std::endl;

      //       bp::child target(targetPath,
      //                        bp::std_in = fp,
      //                        bp::std_out > bp::null, bp::std_err > bp::null);
      //       target.wait();
      //       fclose(fp);
      //       if (target.exit_code() == SIGABRT) {
      //         std::cout << "CRASHED FOR : " << item.path() << std::endl;
      //         fuzzStat.aflExitCode = 0;
      //         break;
      //       }
      //     }
      //   }
      // }
      // else if(seedopt)
	    //   collectInterestingInputs();
      // else {
      //   BOOST_THROW_EXCEPTION(std::runtime_error("Unknown issue with fsolver"));
      //   exit(1);
      // }
    }
    std::cout << "fsolver_main exiting. " << std::endl;
  }
  else
  {
    // orax
    assert(false);
    std::cout << "Dry running without fuzz loop" << std::endl;
    bp::child targetProg(targetPath /*, bp::std_out = aflFuzzOut */);
    targetProg.wait();
    fuzzStat.aflExitCode = targetProg.exit_code();
    if (targetProg.exit_code() == SIGABRT) {
      fuzzStat.crashed = true;
      fuzzStat.timeOut = false;

    }

    fuzzStat.hasInputVars = false;
  }

  fclose(fsolver_out);
  fclose(compile_test_out);

  std::cout << std::endl << termcolor::reset;
  return fuzzStat;
}

FuzzStat Wrafl::fuzz(bool dofuzz) { return fuzz(dofuzz, aflTimeout); }

size_t Wrafl::countQueueSize(void) {
  bfs::path queueDir(std::string("./outdir/queue/default"));
  if (bfs::exists(queueDir))
  {
    // for (bfs::directory_entry& item : bfs::directory_iterator(queueDir))
    // {
    //   if (bfs::is_regular(item))
    //     bfs::copy(item.path(), inDir / item.path().filename());
    // }
    size_t cnt = std::count_if(bfs::directory_iterator(queueDir),
			    bfs::directory_iterator(),
			    static_cast<bool(*)(const bfs::path&)>(bfs::is_regular_file) );
    return cnt;
  }

  return 0;
}

void Wrafl::collectInterestingInputs(void)
{
  // clean up the current input directory
  // copy files from output/crash and output/queue


  std::cout << "Collecting interesting inputs...\n";
  std::cout << "working on : " << inputDirPath << std::endl;
  bfs::path inDir(inputDirPath);
  size_t delstat = bfs::remove_all(inDir);
  std::cout << "input dir cleanup stat : " << delstat << std::endl;

  // create back the directory
  bfs::create_directories(inDir);
  bfs::path queueDir(outputDirPath + std::string("/default/queue"));
  if (bfs::exists(queueDir))
  {
    for (bfs::directory_entry& item : bfs::directory_iterator(queueDir))
    {
      if (bfs::is_regular(item))
        bfs::copy(item.path(), inDir / item.path().filename());
    }
  }

  // TODO : not saving crash inputs as seed
  // only storing interesting inputs from queue
  // Remove crashing inputs from seed directory
  bfs::path crashDir(outputDirPath + std::string("/default/crashes"));
  if (bfs::exists(crashDir))
  {
    for (bfs::directory_entry& item : bfs::directory_iterator(crashDir))
    {
      // TODO: find a better method for getting crash file name
      if (bfs::is_regular(item) && !bfs::exists(inDir / item.path().filename()))
	bfs::copy(item.path(), inDir / item.path().filename());
    }
  }
}


// TODO : method is private now, call validation in input a file path
bool Wrafl::validateCrash(FuzzStat const& fuzzStat)
{
  std::cout << termcolor::blue;
  std::cout << "validating crash..." << std::endl;

  // TODO: check if file exists
  // Also store the exit status of fuzz as a state for this object
  // to be used in validateCrash

  size_t exitcode = 255;
  // std::string crashInputFile(outputDirPath + "/crashes/" + crashInputPath);
  std::string crashInputFile("model.bin");
  FILE* outfp = std::fopen("crash_validation.txt", "wb");

  if (fuzzStat.hasInputVars)
  {
    if (!bfs::exists(crashInputFile))
    {
      std::cout << "Crash input file not found!\n";
      return false;
    }

    FILE* fp = std::fopen(crashInputFile.c_str(), "rb");
    std::cout << "crash file path: " << crashInputFile << std::endl;

    bp::child target(targetPath,
                     bp::std_in = fp,
                     bp::std_out = outfp,
                     bp::std_err = outfp);
    target.wait();
    exitcode = target.exit_code();
    fclose(fp);
    std::cout << "CRASH VALIDATION EXIT CODE : " << exitcode << std::endl;
  }
  else
  {
    bp::child target(targetPath, bp::std_out = outfp, bp::std_err = outfp);
    target.wait();
    exitcode = target.exit_code();
  }

  fclose(outfp);

  if (exitcode == SIGABRT)
  {
    std::cout << termcolor::bold << "[CRASH VALIDATED]" << termcolor::reset
              << std::endl;

    return true;
  }
  else
    std::cout << termcolor::bold << termcolor::red << "CRASH VALIDATION FAILED"
              << termcolor::reset << std::endl;

  return false;
}

bool Wrafl::validatePartialModel(std::string crashInputFile)
{
  std::cout << termcolor::blue;
  std::cout << "validating crash..." << std::endl;

  size_t exitcode = 255;
  FILE* outfp = std::fopen("partial_model_validation.txt", "wb");

  if (!bfs::exists(crashInputFile)) {
    std::cout << "Crash input file not found!\n";
    return false;
  }

  FILE* fp = std::fopen(crashInputFile.c_str(), "rb");
  std::cout << "crash file path: " << crashInputFile << std::endl;

  bp::child target("./a.out",
		   bp::std_in = fp,
		   bp::std_out = outfp,
		   bp::std_err = outfp);
  target.wait();
  exitcode = target.exit_code();
  fclose(fp);
  std::cout << "CRASH VALIDATION EXIT CODE : " << exitcode << std::endl;

  fclose(outfp);

  if (exitcode == SIGABRT)
  {
    std::cout << termcolor::bold << "[CRASH VALIDATED]" << termcolor::reset
              << std::endl;

    return true;
  }
  else
    std::cout << termcolor::bold << termcolor::red << "CRASH VALIDATION FAILED"
              << termcolor::reset << std::endl;

  return false;
}

// TODO: write unit test for collectCrashingInputs
void Wrafl::collectCrashingInputs(void)
{
  bfs::path crashDir(outputDirPath + std::string("/crashes"));
  if (bfs::exists(crashDir))
  {
    for (bfs::directory_entry& item : bfs::directory_iterator(crashDir))
    {
      if (bfs::is_regular(item))
        bfs::copy(item.path(), crashDir / item.path().filename());
    }
  }
}
