from z3.z3 import *

def at_least_one(bool_vars):
  return Or(bool_vars)

def at_most_one(bool_vars, name):
  constraints = []
  n = len(bool_vars)
  s = [Bool(f"s_{name}_{i}") for i in range(n - 1)]
  constraints.append(Or(Not(bool_vars[0]), s[0]))
  constraints.append(Or(Not(bool_vars[n-1]), Not(s[n-2])))
  for i in range(1, n - 1):
      constraints.append(Or(Not(bool_vars[i]), s[i]))
      constraints.append(Or(Not(bool_vars[i]), Not(s[i-1])))
      constraints.append(Or(Not(s[i-1]), s[i]))
  return And(constraints)

def exactly_one(bool_vars, name):
  return And(at_least_one(bool_vars), at_most_one(bool_vars, name))


def output_formatting(text, n_items):
  '''
  return: objective values and couriers' path
  '''
  val = text.split('\n')[0]
  out_ris = []
  counter = 0
  for i in text.split('\n')[1:-1]:
    if (counter == 0 ):
        res = []
    ord =  i.split()[1][:-2]
    if(ord != str(n_items)):
        res.append(int(ord))
        counter = counter + 1
    else: 
        counter = 0
        if (res != []):
            out_ris.append(res)
    

            
  return val, out_ris  


def get_distances_from_path(path, num_items, distances):
  '''
    reuturn: a list m_dist with the distance computed by each courier
  '''
  m_dist = []
  for i in path:
    dist = 0
    prec = num_items
    for j in i:
      dist = dist + distances[prec][j - 1]
      prec = j - 1
    dist = dist +  distances[prec][num_items]
    m_dist.append(dist)
    
  return m_dist