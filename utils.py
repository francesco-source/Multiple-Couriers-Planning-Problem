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
    self.courier_dist_lb = self.set_d_low_bound()
    self.rho_low_bound = self.set_rho_low_bound()
    self.courier_dist_ub = self.set_d_up_bound()
    self.courier_min_load, self. courier_max_load = self.set_min_max_loads()
    self.courier_sort_dict = None

  def set_rho_low_bound(self):  
    """
        Lower bound for the objective function rho
        It is the longest dep->item->dep route possible among the items
    """
    last_row = self.D[-1]
    last_column = self.D[:,-1]
    value1 = last_column[np.argmax(last_row)] + max(last_row)
    value2 = last_row[np.argmax(last_column)] + max(last_column)
    lb = max(value1, value2)
    return lb  
  
  def set_d_low_bound(self):  
    """
        Lower bound for the distance that each courier can travel
        It is the shortest dep->item->dep route possible among the items
    """
    last_row = self.D[-1]
    last_column = self.D[:,-1]
    last_column = last_column[last_column != 0]
    last_row = last_row[last_row !=0]
    value1 = last_column[np.argmin(last_row)] + min(last_row)
    value2 = last_row[np.argmin(last_column)] + min(last_column)
    d_low_bound = min(value1, value2)
    return d_low_bound
  
  def set_d_up_bound(self):
    """
        Upper bound for the distance that each courier can travel, which will also be used as objective function upper bound
        It is the distance of the path [1,2,...,n] (a courier brings all items at once)
    """
    _, n, _, _, D = self.unpack()
              # dep->0    i->i+1 from 0 to n-1              n-1->dep
    up_bound = D[n,0] + np.sum(D[0: n-1, 1: n].diagonal()) + D[n-1, n]    
    return up_bound

  def set_min_max_loads(self):
    min_l = np.min(self.s)
    max_l = np.max(self.l)
    return min_l, max_l
      

  def preprocess_instance(self):    
    """
        Sorts the couriers from the one with the highest capacity to the one with the lowest
        Sets a dictionary that will be used as a map to invert this operation in the post-processing part
    """
    sorted_indices = np.argsort(self.l)[::-1]
    sorted_l_arr = np.array(self.l)[sorted_indices]
    self.l = list(sorted_l_arr)

    self.courier_sort_dict = {i: sorted_indices[i] for i in range(self.m)} 



  def post_process_instance(self,  distances = [], solution = [[]]):
    """
        Inverts the sorting of l and of the solution using the map learned in pre-processing
    """
    if self.courier_sort_dict:
      true_order_distances = list(distances)
      true_order_solution = list(solution)
      for start, end in self.courier_sort_dict.items():
        true_order_solution[end] = solution[start]
        true_order_distances[end] = distances[start]

      return true_order_distances, true_order_solution

    else:
      return distances, solution

  def unpack(self):
    return self.m, self.n, self.s, self.l, self.D


def load_instance(path: str, num: int):
  """
      Creates an Instance of the problem reading input data
      :param path: path of the folder where input data lies
      :param num: number of the instance to retrieve
        :return: the object of class Instance containing the preprocessed data
  """
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

def load_data(path, num):
  """
      Loads all the requested data.
      :param path: path of the folder where input data lies
      :param num: type int -> retrieve instance num 
                        =0 -> retrieve all instances;
            type List[int] -> retrieve instances nums contained in the list
        
        :return: a dictionary in the form {num : Instance num}
  """
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
  """
      Saves the solution dictionary in a .json file
  """
  if not os.path.exists(path):
      os.makedirs(path)
      
  with open(path + filename, 'w') as file:
      json.dump(json_dict, file)
