#!/usr/bin/env python3
"""
@for: the Master Thesis
@written by: Hoang Nguyen Phuoc Bao
"""
import argparse
import os
import shutil
import subprocess
import signal
import configparser as ConfigParser
import json

BASE_DIRECTORY = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

print("Running FGACO with root directory " + BASE_DIRECTORY)

class JSONObject(object):
    def __init__(self, d):
        self.__dict__ = d

def build(conf, skip_tests=False):
    config = ConfigParser.ConfigParser()
    config.read(os.path.join(BASE_DIRECTORY, "execution.ini"))
    set_working_directory(BASE_DIRECTORY)
    if skip_tests:
        subprocess.check_call(config.get('build', 'skipTests'), shell=True)
    else:
        subprocess.check_call(config.get('build', 'default'), shell=True)
        

def execute(conf):
    """
    Execution SQLSI+
    """
    print()
    header = os.path.join(BASE_DIRECTORY, "output", "header.smt2")
    result_file = os.path.join(BASE_DIRECTORY, "output", "theory.smt2")
    if os.path.exists(result_file):
        os.remove(result_file)
    shutil.copy(header, result_file)
    # os.environ['Runs'] = str(conf.Runs)
    path_to_datamodel = os.path.abspath(os.path.join(BASE_DIRECTORY, "src", "main", "resources", "{0}.json".format(conf.DataModel)))
    os.environ['PATHTODATAMODEL'] = path_to_datamodel
    print("[DataModel] " + path_to_datamodel)
    path_to_securitymodel = os.path.abspath(os.path.join(BASE_DIRECTORY, "src", "main", "resources", "{0}.json".format(conf.SecurityModel)))
    os.environ['PATHTOSECURITYMODEL'] = path_to_securitymodel
    print("[SecurityModel] " + path_to_securitymodel)
    if hasattr(conf, 'Invariants'):
        os.environ['INVARIANTS'] = "##".join(conf.Invariants)
        print("[Invariants] ")
        for iInv, inv in enumerate(conf.Invariants):
            print("  " + str(iInv) + ". " + inv)
    os.environ['ROLE'] = conf.Role
    print("[Role] " + conf.Role)
    # print("Action: READ")
    if hasattr(conf.Resource, 'Association'):
        os.environ['ASSOCIATION'] = conf.Resource.Association
        print("[Resource] (" + conf.Resource.Association + ")")
    else:
        os.environ['ENTITY'] = conf.Resource.Entity
        os.environ['ATTRIBUTE'] = conf.Resource.Attribute
        print("[Resource] (" + conf.Resource.Entity + ":" + conf.Resource.Attribute + ")")
    if hasattr(conf, 'Properties'):
        os.environ['PROPERTIES'] = "##".join(conf.Properties)
        print("[Properties] ")
        for iProp, prop in enumerate(conf.Properties):
            print("  " + str(iProp) + ". " + prop)
    if not hasattr(conf, 'Timeout'):
        conf.Timeout = 10000
    print("[Timeout] {0}".format(conf.Timeout))
    # os.environ['CHECKAUTHORIZED'] = conf.CheckAuthorized
    # print("Check authorized: " + conf.CheckAuthorized)
    os.environ['CHECKAUTHORIZED'] = "true"

    print("[INFO] Generating MSFOL theory...")
    print("[INFO]")
    print("[INFO] ------------------------------------------------------------------------")
    config = ConfigParser.ConfigParser()
    config.read(os.path.join(BASE_DIRECTORY, "execution.ini"))
    try:
        # instead of subprocess.check_output()
        # to enforce timeout before Python 3.7.5
        # and kill sub-processes to avoid interference
        # https://stackoverflow.com/a/36955420
        with subprocess.Popen(config.get('run', 'cmd'), shell=True, stdout=subprocess.PIPE,
                                start_new_session=True) as process:
            try:
                import time
                start_time = time.time()
                stdout, stderr = process.communicate(timeout=conf.Timeout)
                end_time = time.time()
                print("[INFO] GENERATE SUCCESS")
                print("[INFO] ------------------------------------------------------------------------")
                print("[INFO] Total time: {0} s".format(round(end_time-start_time,3)))
                print("[INFO] Stored at: {0}".format(result_file))
                print("[INFO] ------------------------------------------------------------------------")
                print()
                return_code = process.poll()
                if return_code:
                    raise subprocess.CalledProcessError(return_code, process.args,
                                                        output=stdout, stderr=stderr)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGINT)  # send signal to the process group
                raise
        with open(result_file, "ab") as file:
            file.write(stdout)
    except subprocess.TimeoutExpired as e:
        print("[ERROR] Program reached the timeout set ({0} seconds)".format(e.timeout))
        print("[ERROR] The command we executed was '{0}'".format(e.cmd))
        print()

def clean_dir(*path):
    dir = os.path.join(BASE_DIRECTORY, *path)
    if os.path.exists(dir):
        shutil.rmtree(dir)
    os.mkdir(dir)


def set_working_directory(*path):
    dir = os.path.join(BASE_DIRECTORY, *path)
    os.chdir(dir)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("-b", "--build",
                        help="build the project",
                        action="store_true")
    parser.add_argument("-e", "--execute",
                        help="execute the SQLSI+",
                        action="store_true")    
    parser.add_argument("-c", "--config-file",
                        help="configuration file",
                        dest='testcase',
                        action="store")
    args = parser.parse_args()
    CONFIG_FILENAME = args.testcase + ".json"


    set_working_directory("config")
    with open(CONFIG_FILENAME, "r") as config_file:
        config = json.load(config_file, object_hook=JSONObject)

    # if there are no args, execute a full sequence
    # with the test and the visualization/reporting
    no_args = all(not val for val in vars(args).values())

    if args.build or no_args:
        build(config)
    if args.execute or no_args:
        execute(config)
