import sys
import pathlib
import os
import subprocess

COMPILE_COMMAND = "compile"
GENERATE_PROJECT_FILE_COMMAND = "genprojf"
COMMANDS = [COMPILE_COMMAND, GENERATE_PROJECT_FILE_COMMAND]

NO_COMMAND_MESSAGE = "Please use one of the commands: " + ", ".join(COMMANDS)
UNKNOWN_COMMAND_MESSAGE = NO_COMMAND_MESSAGE
FATAL_COMPILATION_ERROR_MESSAGE = "!!!===========FATAL ERROR: COMPILATION FAILED===========!!!"
COMPILATION_SUCCESS_MESSAGE = "COMPILATION SUCCESSFUL"
GENPROJF_SUCCESS_MESSAGE = "COQ PROJECT FILE SUCCESSFULLY GENERATED"

COQ_SOURCE_EXT = ".v"
COQ_COMPILED_EXT = ".vo"
COQ_COMPILER = "coqc"
COQ_COMPILER_DISPLAY_ALL_WARNINGS = "-w all"
COQ_COMPILER_OUTPUT_FLAG = "-o"
COQ_PROJECT_FILE_NAME = "_CoqProject"

VERINNCOQ_ROOT = os.path.dirname(os.path.abspath(__file__))
VERINNCOQ_TARGET_DIRECTORY = os.path.join(VERINNCOQ_ROOT, "target")
VERINNCOQ_COMPILE_PARAMS = ["-R " + VERINNCOQ_TARGET_DIRECTORY + " Verinncoq"]
VERINNCOQ_FILES = [
    #Folder, name without extension, skip
    (".", "real_subsets", False),
    (".", "reals_real_subset", False),
    (".", "real_subsets_instances", False),
    (".", "matrix_extensions", False),
    (".", "fourier_motzkin", False),
    (".", "piecewise_affine", False),
    (".", "pwaf_operations", False),
    (".", "neuron_functions", False),
    (".", "neural_networks", False),
    (".", "NNDH", False),
    (".", "fourier_motzkin", False),
    (".", "NNDH_to_fme", False),
    (".", "fm_q_support", False)
]

VERINNCOQ_COQ_PROJECT_FILE = "-R " + VERINNCOQ_ROOT.replace(os.sep, "/") + "/target Verinncoq"
VERINNCOQ_CACHE_DIR = "__verinncache__"

def compile_file(source_folder, file_without_ext, target_folder, coqc_params, skip, verbose):
    pathlib.Path(target_folder).mkdir(parents=True, exist_ok=True)
    if skip:
        return
    input_file = os.path.join(source_folder, file_without_ext + COQ_SOURCE_EXT)
    output_file = os.path.join(target_folder, file_without_ext + COQ_COMPILED_EXT)
    coqc_params_string = " ".join(coqc_params)
    command = " ".join(
                    [COQ_COMPILER, COQ_COMPILER_DISPLAY_ALL_WARNINGS, coqc_params_string, 
                    input_file, COQ_COMPILER_OUTPUT_FLAG, output_file]
                )
    if verbose:
        print(command)
    return_code = subprocess.call(command, shell=True)
    return return_code == 0

def compile_verinncoq_file(local_folder, file_without_ext, skip):
    full_folder = os.path.join(VERINNCOQ_ROOT, local_folder)
    return compile_file(full_folder, file_without_ext, VERINNCOQ_TARGET_DIRECTORY, VERINNCOQ_COMPILE_PARAMS, skip, True)

def generate_coq_project_file():
    with open(COQ_PROJECT_FILE_NAME, "w") as f:
        f.write(VERINNCOQ_COQ_PROJECT_FILE)

def main():
    if len(sys.argv) < 2:
        print(NO_COMMAND_MESSAGE)
        return
    
    if sys.argv[1] == COMPILE_COMMAND:
        for folder, file, skip in VERINNCOQ_FILES:
            if not compile_verinncoq_file(folder, file, skip):
                print(FATAL_COMPILATION_ERROR_MESSAGE)
                return
        print(COMPILATION_SUCCESS_MESSAGE)

    elif sys.argv[1] == GENERATE_PROJECT_FILE_COMMAND:
        generate_coq_project_file()
        print(GENPROJF_SUCCESS_MESSAGE)

    else:
        print(UNKNOWN_COMMAND_MESSAGE)

if __name__ == "__main__":
    main()