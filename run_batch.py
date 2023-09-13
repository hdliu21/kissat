import os
import subprocess
import shutil

# get the list of input files in the input folder
input_files = os.listdir("/data/hdliu21/github/sat_2018")

cnf_file = []
for file_name in input_files:
  if file_name.endswith(".cnf"):
    cnf_file.append(file_name)
# set the batch size to 20
batch_size = 20

# Get the current directory
current_directory = os.getcwd()

# Specify the directory name
directory_name = "logs"

# Create or delete files in the directory based on its existence
directory_path = os.path.join(current_directory, directory_name)
if os.path.exists(directory_path):
    # Delete all files in the directory
    file_list = os.listdir(directory_path)
    for file_name in file_list:
        file_path = os.path.join(directory_path, file_name)
        if os.path.isfile(file_path):
            os.remove(file_path)
            print(f"Deleted file: {file_name}")
else:
    # Create the directory
    os.mkdir(directory_path)
    print(f"Directory '{directory_name}' created successfully.")
# loop through the input files in batches
for i in range(0, len(cnf_file), batch_size):
    # get the current batch of files
    batch_files = cnf_file[i:i+batch_size]
    process_list = []
    # loop through each file in the batch
    for file in batch_files:
        # get the full path of the file
        file_path = os.path.join("/data/hdliu21/github/sat_2018", file)
        
        # get the name of the log file
        log_file = file + ".log"
        
        # get the full path of the log file
        log_path = os.path.join("logs", log_file)
        
        
        # open the log file for writing
        with open(log_path, "w") as f:
            # execute the a.out program with the file as input and redirect the output to the log file
            p = subprocess.Popen(["./kissat", "-q", "--time=600", "-n", file_path], stdout=f, stderr=f)
            process_list.append(p)
        # print a message to indicate the progress
        print(f"Executed {file} and saved log to {log_file}")
    for p in process_list:
      p.wait()
    # print a message to indicate the end of the batch
    print(f"Finished batch {i//batch_size + 1}")
