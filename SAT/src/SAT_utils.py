from itertools import combinations
from z3 import *
import math
import numpy as np


## MANIPULATE NUMBERS

def toBinary(num, length = None, dtype = int):
  num_bin = bin(num).split("b")[-1]
  if length:
      num_bin = "0"*(length - len(num_bin)) + num_bin
  num_bin = [dtype(int(s)) for s in num_bin]
  return num_bin


def toInteger(bool_list):
  binary_string = ''.join('1' if b else '0' for b in bool_list)
  return int(binary_string, 2)


## SIMPLER CONSTRAINT ENCODINGS

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

def lesseq(a, b):
  """
  a and b are lists of variables of equal length containing each the binary
  encoding of an integer number. The constraint is true if a is less than or
  equal to b
  """
  constraints = []
  constraints.append(Or(Not(a[0]),b[0]))
  for i in range(1,len(a)):
    constraints.append(Implies(And([a[k] == b[k] for k in range(i)]), Or(Not(a[i]),b[i])))
  return And(constraints)

def equals(a, b):
  return And([a[i] == b[i] for i in range(len(a))])

def one_bit_full_adder(a, b, c_in, s, c_out):
    xor_ab = Xor(a, b)
    constr_1 = s == Xor(xor_ab, c_in)
    constr_2 = c_out == Or(And(xor_ab, c_in), And(a, b))
    return And(constr_1, constr_2)

def full_adder(a, b, d, name= ""):
  if len(a)==len(b):
    n = len(a)
  elif  (len(a)>len(b)):
    n = len(a)
    b = [BoolVal(False)] * (len(a) - len(b)) + b  
  else:
    n = len(b)
    a = [BoolVal(False)] * (len(b) - len(a)) + a

  c = [Bool(f"carry_{name}_{i}") for i in range(n)] + [BoolVal(False)]

  constr = []

  for i in range(n):
    constr.append(one_bit_full_adder(a= a[n-i-1], b= b[n-i-1], c_in= c[n - i], s= d[n - i - 1], c_out= c[n - i - 1]))
  constr.append(Not(c[0]))
  return And(constr)

def sum_vec(vec, s, name= ""):
  if len(vec) == 2:
    return full_adder(a= vec[0], b= vec[1], d= s, name= name)
  elif len(vec) == 1:
    return equals(vec[0], s)
  else:
    partial = [[Bool(f"p_{name}_{i}_{b}") for b in range(len(vec[0]))] for i in range(len(vec) - 2)]
    constr = []
    constr.append(full_adder(vec[0], vec[1], partial[0], name= name+"0"))
    for i in range(len(vec)-3):
      constr.append(full_adder(partial[i], vec[i+2], partial[i+1], name= name+str(i+1)))
    constr.append(full_adder(partial[-1], vec[-1], s, name= name+"last"))
    return And(constr)

def maximum(vec, maxi, name= ""):
  if len(vec) == 1:
    return equals(vec[0], maxi)
  elif len(vec) == 2:
    constr1 = Implies(lesseq(vec[0], vec[1]), equals(vec[1], maxi))
    constr2 = Implies(Not(lesseq(vec[0], vec[1])), equals(vec[0], maxi))
    return And(constr1, constr2)
  
  par = [[Bool(f"maxpar_{name}_{i}_{b}") for b in range(len(maxi))] for i in range(len(vec)-2)]
  constr = []

  constr.append(Implies(lesseq(vec[0], vec[1]), equals(vec[1], par[0])))
  constr.append(Implies(Not(lesseq(vec[0], vec[1])), equals(vec[0], par[0])))

  for i in range(1, len(vec)-2):
    constr.append(Implies(lesseq(vec[i+1], par[i-1]), equals(par[i-1], par[i])))
    constr.append(Implies(Not(lesseq(vec[i+1], par[i-1])), equals(vec[i+1], par[i])))

  constr.append(Implies(lesseq(vec[-1], par[-1]), equals(par[-1], maxi)))
  constr.append(Implies(Not(lesseq(vec[-1], par[-1])), equals(vec[-1], maxi)))
  
  return And(constr)