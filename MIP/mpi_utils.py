import numpy as np
from pulp import *


def And(model, a, b, name):
        """
        And(a,b)
        :param a: first parameter of And condition
        :param b: second parameter of And condition
        :param name: name of the And
        :return: 1 if a and b is true, false otherwise
        """
        delta = LpVariable(cat=LpInteger, name=name)
        model += delta <= a
        model += delta >= a + b - 1
        model += delta >= 0
        model += delta <= b
        return delta


def linear_prod(model, binary_var, countinuos_var, ub, name):
        """
        res = binary_var * countinuos_var
        :param binary_var: binary variable
        :param countinuos_var: countinuos variable
        :param ub: upper bound of the countinuos variable
        :param name: name of the product
        :return: the result of the product
        """
        res = LpVariable(cat=LpInteger, name=name)
        model += ub * binary_var >= res
        model += countinuos_var >= res
        model += countinuos_var - (1 - binary_var) * ub <= res
        model += res >= 0
        return res  

M = 1000

def If(model, a, b, M, name):
    delta = LpVariable(cat=LpBinary, name=name)
    model += a - b <= M * delta
    model += b - a <= M * (1 - delta)
    return delta


