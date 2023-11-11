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
