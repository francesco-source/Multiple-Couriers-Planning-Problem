import numpy as np
import os
import json

class Instance:
    def __init__(self, m, n, l, s, D):
        self.m = m
        self.n = n
        self.l = l
        self.s = s
        self.D = np.array(D)
        self.correspondences = None
        self.corr_inverse = None
        
    def preprocess_instance(self):
        self.correspondences = np.argsort(self.l)[::-1]
        transformation_function = sorted(zip(self.correspondences, np.arange(self.m)))
        self.corr_inverse = np.fromiter((x for _, x in transformation_function), dtype= int)
        
        self.l = sorted(self.l, reverse= True)
        # np.array(inst.l)[corr_inverse] to invert the sorting of l
    def unpack(self):
      return self.m, self.n, self.s, self.l, self.D
        
def load_instance(path: str, num: int):
  if num < 10:
    num = "0"+str(num)
  else:
    num = str(num)
  path += f"/inst{num}.dat"
  file = open(path, 'r')
  
  m = int(file.readline())
  n = int(file.readline())
  l = [int(x) for x in file.readline().split(" ") if x!= ""]
  s = [int(x) for x in file.readline().split(" ") if x!= ""]
  D = []
  for i in range(n+1):
      D.append([int(x) for x in file.readline().split(" ") if x!= "\n" if x!= ""])
  
  instance = Instance(m, n, l, s, D)
  instance.preprocess_instance()
  return instance

def load_data(path: str, num):
  if type(num) == int:
    if 0 < num <= 21:
      return {str(num): load_instance(path, num)}
    elif num == 0:
      return {str(x): load_instance(path, x) for x in range(1, 22)}
    else:
      raise ValueError("The specified instance ID is wrong: expected between 1 and 21")
  
  elif type(num) == list:
    return {str(x): load_instance(path, x) for x in num}
  
  else:
    raise TypeError("The number of instance should be either an integer or a list of integers")
  
def save_file(path, filename, json_dict):
  if not os.path.exists(path):
      os.makedirs(path)
      
  with open(path + filename, 'w') as file:
      json.dump(json_dict, file)
