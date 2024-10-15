
#include "aufbv-wrafl.h"

#include <unistd.h>

#include <boost/filesystem.hpp>
#include <boost/lambda/bind.hpp>
#include <boost/process.hpp>
#include <boost/throw_exception.hpp>
#include <boost/process/environment.hpp>
#include <boost/thread.hpp>

#include <cstdio>
#include <iostream>
#include <set>
#include <termcolor.hpp>

#include <chrono>
#include <unistd.h>
#include "fsolve.h"

using namespace std;


namespace bfs = boost::filesystem;
namespace bp = boost::process;

std::string CMD_ARGV0 = "";

static std::string readfile(FILE* fp){
  int filesize;
  std::string data = "";
  fseek(fp, 0, SEEK_END);
  filesize = ftell(fp);
  char* file_contents = (char*)(malloc(filesize+1));
  auto _ = fread(file_contents, filesize, 1, fp);
  file_contents[filesize] = '\0';
  std::string content(file_contents);
  free(file_contents);
  return content;
}

static std::string get_file_dir(std::string filepath){
  std::string dir = "";
  for(int i = filepath.size()-1; i >= 0; i--){
    if(filepath[i] == '/'){
      dir = filepath.substr(0, i);
      break;
    }
  }
  return dir;
}

AUFBVWrafl::AUFBVWrafl(std::string srcfile,
             std::string libfile,
             std::string indir,
             std::string outdir,
             unsigned aflTOut)
    : srcPath(srcfile),
      libPath(libfile),
      targetPath("./test.out"),
      inputDirPath(indir),
      outputDirPath(outdir),
      aflTimeout(aflTOut),
      crashInputPath(), seedopt(true) {}

bool AUFBVWrafl::checkSetup(void)
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

AUFBVFuzzStat AUFBVWrafl::fuzz(bool dofuzz, unsigned int timeout)
{
  AUFBVFuzzStat fuzzStat;
  // orax
  FILE* fsolver_out = fopen("fsolver.log", "w");
  FILE* compile_test_out = fopen("compile_test.log", "w");
  if (dofuzz)
  {
    // orax
    auto start = chrono::steady_clock::now();

    // compile dlib: TODO: debug
    std::string compilerPath = "TODO: compiler path";
    std::string compileTestCommand = compilerPath + " -shared target.c " + libPath + " -o target.so";
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

    std::string compileTestCommand1 = compilerPath + " target.c " + libPath + " -o test.out";
    std::cout << termcolor::blue;
    std::cout << "Compile Test command : " << compileTestCommand1 << std::endl;
    auto compile_test_env1 {boost::this_process::environment()};
    bp::child compile_test1(compileTestCommand1, compile_test_env1, bp::std_out > compile_test_out, bp::std_err > compile_test_out);
    if (!compile_test1.wait_for(std::chrono::seconds(timeout)))
    {
      fuzzStat.timeOut = true;
      compile_test1.terminate();
    }
    compile_test1.wait();

    // launch fsolver
    bool libsolve = false;
    if (libsolve){
      // FIXME: unfinished libsolve
      assert(false);
    }
    else{
      std::string fsolver_path = "TODO: fsolver path";
      std::string launchCommand = fsolver_path + " -l ./target.so";
      auto fsolver_env {boost::this_process::environment()};
      std::cout << termcolor::blue;
      std::cout << "Fsolver command : " << launchCommand << std::endl;
      bp::child fsolver_main(launchCommand, fsolver_env, bp::std_out > fsolver_out, bp::std_err > fsolver_out);
      // if (!fsolver_main.wait_for(std::chrono::seconds(timeout)))
      if (!fsolver_main.wait_for(std::chrono::seconds(30)))
      {
        fuzzStat.timeOut = true;
        fsolver_main.terminate();
      }
      fsolver_main.wait();
      std::cout << "fsolver main exit code : " << fsolver_main.exit_code() << std::endl;
      fuzzStat.aflExitCode = fsolver_main.exit_code();
      std::cout << "fsolver_main timed out : " << fuzzStat.timeOut << std::endl;
    }

    auto stop = chrono::steady_clock::now();
    std::cout << "TIME taken: " << chrono::duration_cast<chrono::milliseconds>(stop - start).count() << "sec" << std::endl;

    if (fuzzStat.timeOut) {
      std::cout << "YES TIMEOUT\n";
      fuzzStat.crashed = false;
      fuzzStat.timeOut = true;
    }
    else {
      std::cout << "NO TIMEOUT\n";
      fuzzStat.crashed = false;
      fuzzStat.timeOut = false;

      std::cout << "Checking for possible crashing seed input..." << std::endl;
      std::ifstream in("solution.bin");
      std::string line;
      if (in){
        std::cout << "SAT!" << std::endl;
        fuzzStat.crashed = true;
      }
      else{
        std::cout << "No solution.bin file found" << std::endl;
      }
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

AUFBVFuzzStat AUFBVWrafl::fuzz(bool dofuzz) { return fuzz(dofuzz, aflTimeout); }

size_t AUFBVWrafl::countQueueSize(void) {
  bfs::path queueDir(std::string("./outdir/queue/default"));
  if (bfs::exists(queueDir))
  {
    size_t cnt = std::count_if(bfs::directory_iterator(queueDir),
			    bfs::directory_iterator(),
			    static_cast<bool(*)(const bfs::path&)>(bfs::is_regular_file) );
    return cnt;
  }

  return 0;
}

void AUFBVWrafl::collectInterestingInputs(void)
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
bool AUFBVWrafl::validateCrash(AUFBVFuzzStat const& fuzzStat)
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

bool AUFBVWrafl::validatePartialModel(std::string crashInputFile)
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
  std::string file_contents = readfile(fp);
  std::string cmdline = "./test.out \"" + std::string(file_contents) +"\"";
  std::cout << " cmdline: " << cmdline << std::endl;
  bp::child target(cmdline.c_str(),
		   bp::std_in = fp,
		   bp::std_out = outfp,
		   bp::std_err = outfp);
  target.wait();
  exitcode = target.exit_code();
  fclose(fp);
  std::cout << "CRASH VALIDATION EXIT CODE : " << exitcode << std::endl;

  fclose(outfp);
  // free(file_contents);
  // if (exitcode == SIGABRT)
  if (exitcode == 0)
  {
    std::cout << termcolor::bold << "[VALID INPUT]" << termcolor::reset
              << std::endl;

    return true;
  }
  else
    std::cout << termcolor::bold << termcolor::red << "FAILED INPUT"
              << termcolor::reset << std::endl;

  return false;
}

// TODO: write unit test for collectCrashingInputs
void AUFBVWrafl::collectCrashingInputs(void)
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
