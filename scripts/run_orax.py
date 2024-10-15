#!/usr/bin/python3

import subprocess
import sys
import csv
import os
import threading
import signal
import psutil
import re
import fnmatch
import shutil
import statistics as stats
import time

from optparse import OptionParser

# ORAX_BIN from Environment
ORAX_BIN = os.getenv('ORAX_BIN')
if ORAX_BIN is None:
    print("ORAX_BIN environment variable is not set.")
    exit()
elif not os.path.exists(ORAX_BIN):
    print("ORAX_BIN path does not exist.")
    exit()
else:
    print("ORAX_BIN path is set to:", ORAX_BIN)
PROJECT_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BENCHDIR= os.path.abspath('{}/benchmarks-run'.format(PROJECT_DIR))
if not os.path.exists(BENCHDIR):
    print("Experiment directory is not prepared. Please run ./prepare_enviroment.sh first.")
    exit()
else:
    print("Experiment directory {} is ready.".format(BENCHDIR))
RESULTDIR=os.getcwd()
TODAY_DATE = time.strftime("%Y%m%d_%H%M%S")
RESULT_CSV="orax_{}.csv".format(TODAY_DATE)

""" Exit Codes """
EXIT_OK = 0
EXIT_FAILURE = 1
COMPILE_FAILURE = 2
STATUS_TIMEOUT = 3

DIDNOTRUN = []

def get_median_record(solver_stat_list):
    timeout_list = [rec['total_time'] for rec in solver_stat_list]
    median_timeout = stats.median(timeout_list)
    for rec in solver_stat_list:
        if rec['total_time'] == median_timeout:
            return rec

def kill_children(pid):
    parent = psutil.Process(pid)
    children = parent.children(recursive=True)
    for child in children:
        try:
            child.kill()
        except psutil.NoSuchProcess:
            pass
    parent.kill()

def runSingleBench(filename, LIB, options):
    # copy execution script
    shutil.copyfile('{}/scripts/run_test_orax.sh'.format(PROJECT_DIR), CWD + '/run_test_orax.sh')
    os.chmod('run_test_orax.sh', 0o777)

    timeout = options.timeout
    print("Creating static lib for:", LIB)
    """ For each benchmark directory compile the library first """

    results = open(RESULTDIR + '/' + RESULT_CSV, mode='a')
    dictwriter_object = csv.DictWriter(results, fieldnames=['filename', 'total_time', 'status'])

    print("Evaluating file:", filename)
    trials = options.iters
    solver_stat_list = []
    while trials > 0:
        trials = trials - 1
        iterno = options.iters - trials
        outfile = open('out.txt', 'w')
        errfile = open('stats.csv', 'w')
        solver_stat = {'total_time' : 0}
        proc = subprocess.Popen([CWD + '/run_test_orax.sh', ORAX_BIN, filename, LIB], stdout=outfile, stderr=errfile)
        exit_status = STATUS_TIMEOUT
        try:
            if timeout:
                timer = threading.Timer(timeout, lambda p: kill_children(p.pid), [proc])
                timer.start()
            _,_ = proc.communicate(input=None)
            exit_status = proc.returncode
        finally:
            if timeout:
                if exit_status == -9 and not timer.is_alive():
                    exit_status = STATUS_TIMEOUT
                timer.cancel()
        time.sleep(1)
        if exit_status == -6:
            DIDNOTRUN.append(filename)
            continue
        solver_stat['filename'] = filename
        solver_stat['status'] = 'unknown'
        if exit_status == STATUS_TIMEOUT:
            solver_stat['total_time'] = timeout
            solver_stat['status'] = 'unknown'
        else:
            # prune the stats file
            with open('stats.csv', 'r') as f:
                lines = f.readlines()
                flag = False
                new_lines = []
                for line in lines:
                    if flag:
                        new_lines.append(line)
                    if 'DefaultModel::ee::constantTermsCount' in line:
                        flag = True
                        new_lines.append(line[:line.find('DefaultModel::ee::constantTermsCount')])
                with open('pruned_stats.csv', 'w') as fo:
                    fo.writelines(new_lines)
            stats_file = open('pruned_stats.csv', "r")
            csv_file = csv.reader(stats_file, delimiter=",")
            # read statistics
            try:
                for row in csv_file:
                    if row[0] == 'driver::totalTime':
                        solver_stat['total_time'] = round(float(row[1].strip()), 3)
                    elif row[0] == 'driver::sat/unsat':
                        solver_stat['status'] = row[1].strip()
            except IndexError:
                print(f"something went wrong for iteration #{iterno}")
                solver_stat['total_time'] = timeout
                solver_stat['status'] = 'unknown'
            stats_file.close()
        print(f"Iteration #{iterno}:, status: {solver_stat['status']}, total time: {solver_stat['total_time']}")
        solver_stat_list.append(solver_stat)
        outfile.close()
        errfile.close()
    median_stat = get_median_record(solver_stat_list)
    print("Median Runtime:", median_stat["total_time"])
    dictwriter_object.writerow(median_stat)
    results.close()

def getBenchById(benchId):
    bench_namemap_csv = open("{}/scripts/benchmark_name_mapping.csv".format(PROJECT_DIR), "r")
    bench_name_reader = csv.DictReader(bench_namemap_csv)
    for row in bench_name_reader:
        if int(row["Benchmark"]) == benchId:
            bench_namemap_csv.close()
            return row["Path"]

if __name__=="__main__":
    parser = OptionParser()
    parser.add_option("--iters", dest="iters", type="int", help="total no. of runs for each benchmark (default 1)", default=1)
    parser.add_option("-t", "--timeout", type="int", dest="timeout", help="set solver timeout", default=600)
    parser.add_option("--bench-list", type="string", dest="bench_list", help="file with a list of benchmakrs ids to run", default = None)
    opts, args = parser.parse_args()

    if len(sys.argv) < 2:
        parser.print_help()
        sys.exit(1)

    if int(opts.iters) % 2 == 0 :
        print("No. of iterations in --iters should be an odd number")
        parser.print_help()
        exit()

    with open(RESULT_CSV, 'w', newline='') as outcsv:
        writer = csv.writer(outcsv)
        writer.writerow(['filename', 'total_time', 'status'])

    if opts.bench_list:
        print("Reading benchmark list:", opts.bench_list)
        list_file = open(opts.bench_list, "r")
        line = list_file.readline().strip()
        for bid in line.split(','):
            filepath = getBenchById(int(bid))
            CWD = os.path.dirname(filepath)
            os.chdir(CWD)
            DESCFILE=open("DESC", 'r')
            LIB=DESCFILE.readline().strip()
            DESCFILE.close()
            runSingleBench(filepath, LIB, opts)
    else:
        print("No benchmark list provided.")