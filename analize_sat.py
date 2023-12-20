from utils import load_data
import pandas as pd
import json
import numpy as np

input_folder = "./input"
output_folder = "./res/SAT"

data = load_data(input_folder, list(range(1, 11)))

scores = {}
for i, instance in data.items():
    s = np.array(instance.s)
    s = (s - np.min(s))/(np.max(s) - np.min(s))
    scores[i] = np.std(s)
df_scores = pd.DataFrame.from_dict(scores, orient= "index", columns= ["scaled std"])

# Function to read JSON file
def read_json_file(file_path):
    with open(file_path, 'r') as file:
        data = json.load(file)
    return data

data_dict = {}
entries_to_keep = ["linear_no_sb", "linear_no_sb_heu", "binary_no_sb", "binary_no_sb_heu"]

for i in range(1, 11):
    file_path = output_folder + f"/{i}.json"

    data = read_json_file(file_path)
    i_dict = {}
    
    for entry in entries_to_keep:
        i_dict[entry] = {"time" : data[entry]["time"], "optimal": data[entry]["optimal"]}
    

    data_dict[i] = i_dict

df_inst = pd.DataFrame.from_dict(data_dict, orient='index')

print(df_scores)
print(df_inst)