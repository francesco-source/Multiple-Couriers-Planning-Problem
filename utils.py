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
        self.ratio_courier_loads = np.max(l)//np.min(l)
        self.courier_dist_lb = self.set_d_low_bound()
        self.courier_dist_ub = self.set_d_up_bound()
        self.rho_low_bound = self.set_rho_lower_bound()
        self.courier_min_load, self. courier_max_load = self.set_min_max_loads()
        self.correspondences = None
        self.corr_inverse = None
        self.courier_sort_dict = None


    def set_rho_lower_bound(self):  
        last_row = self.D[-1]
        last_column = self.D[:,-1]
        value1 = last_column[np.argmax(last_row)] + max(last_row)
        value2 = last_row[np.argmax(last_column)] + max(last_column)
        lb = max(value1, value2)
        return lb  
    
    def set_d_low_bound(self):  
       d_low_bound = int(np.min(self.D[self.D.nonzero()]) * (self.n/self.m +1))
       return d_low_bound
    
    def set_d_up_bound(self):
       up_bound = np.max(self.D)*self.n //self.m + np.max(np.array(self.D)[:,-1])
       return up_bound
    
    def set_min_max_loads(self):
      min_l = np.min(self.s) * self.n // self.m
      max_l = np.sum(np.partition(self.s, self.m)[self.m-1:]) if np.sum(np.partition(self.s, self.m)[self.m:]) <= max(self.l) else max(self.l)

      return min_l, max_l
    
        
    def sort_l(self):
      sorted_list = sorted(self.l,reverse = True)
      sorting_dict = {}

      for index, element in enumerate(self.l):
            if element not in sorting_dict:
                sorting_dict[element] = []
            sorting_dict[element].append([index, sorted_list.index(element)])

      return sorted_list, sorting_dict
    

    def preprocess_instance(self):
        self.correspondences = np.argsort(self.l)[::-1]
        transformation_function = sorted(zip(self.correspondences, np.arange(self.m)))
        self.corr_inverse = np.fromiter((x for _, x in transformation_function), dtype= int)

        self.l, self.courier_sort_dict = self.sort_l()
        
        #self.l = sorted(self.l, reverse= True)
        # np.array(inst.l)[corr_inverse] to invert the sorting of l
      
    def post_process_instance(self, package_vec_res):
        # Given the instance and the result of each package carried by each courier,
        # sort the packages using the courier_sort_dictionary.

        # Create a temporary list with pairs (dictionary value, original list index).
        temp = [(self.courier_sort_dict[val][0], val, self.courier_sort_dict[val][1])
                 for val in self.courier_sort_dict]

        # Sort the temporary list based on dictionary values.
        temp.sort()
        # Build the result list 'package_ordered' by rearranging elements of 'package_vec_res'
        # based on the indices obtained from the temporary list.
        package_ordered = [package_vec_res[index] for _, _, index in temp]

        return package_ordered


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
