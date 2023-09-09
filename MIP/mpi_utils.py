import numpy as np

class Mcpp_var:
     def __init__(self, m, n, l, s, D):
        self.m = m
        self.n = n
        self.l = l
        self.s = s
        self.D = D


def load_instances(num: int):
  if num < 10:
    num = "0"+str(num)
  else:
    num = str(num)
  
  file = open(f"../input/inst{num}.dat", 'r')
  
  m = int(file.readline())
  n = int(file.readline())
  l = [int(x) for x in file.readline().split(" ") if x!= ""]
  s = [int(x) for x in file.readline().split(" ") if x!= ""]
  D = []
  for i in range(n+1):
      D.append([int(x) for x in file.readline().split(" ") if x!= "\n" if x!= ""])
  
  return Mcpp_var(m, n, l, s, D)    

