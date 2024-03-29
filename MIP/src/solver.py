from pulp import *
import numpy as np
from utils import *
import time as t
from MIP.src.mip_utils import *
from constants import *
import copy

class MIPsolver:

    def __init__(self, data, output_dir, timeout = 270, mode = 'v'):

        self.data = data
        self.output_dir = output_dir
        self.timeout = timeout
        self.solver = None
        self.mode = mode


    def set_solver(self,name = f"solve_instance",sense = LpMinimize):
        '''
        Defines solver and Lp problem 
        '''
        self.solver = LpProblem(name = name, sense = sense)

    
    def solve(self):
        """
            Runs the solver and saves the results:
                - for each data instance
                - for each solving strategy option
        """
        path = self.output_dir + "/MIP/"
        for num, instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for strategy, stratstr in STRATEGIES_MIP_DICT.items():
                for sym , symstr in SYM_DICT_MIP.items():
                    for sub_tour_k, sub_tour_v in SUB_TOURS_MIP_DICT.items():  
                    
                        self.set_solver()
                        
                        variables = self.model1(instance,sub_tour_v)
                        if sym == SYMMETRY_BREAKING:
                         self.add_sb_constraint(instance,variables)
                        time, optimal, obj,res = self.search(instance,variables,strategy,sub_tour_v)
                        self.print_obj_dist(obj,sym,stratstr,sub_tour_v)

                        key_dict =  stratstr + sub_tour_v
                        json_dict[key_dict] = {"time" : time, "optimal": optimal, "obj": obj, "sol": res}
                        if self.mode == 'v':
                            print()
                    if self.mode == 'v':
                        print()
            print()          

            save_file(path, num + ".json", json_dict)

    def print_obj_dist(self,obj,sym,strastr,sub_t = "_mtz"):
        print(f"Max distance found using {strastr} solver,{' without sb :' if sym==NO_SYMMETRY_BREAKING else ''} {obj}")
        print("subtour elimination used = ", sub_t)


    def search(self,instance,variables,strategy,sub_tour_elimination = "_mtz"):
        """
            Runs the  search with the specified sub tour elimination formulutaions
            :return
                time: time needed to solve the instance
                optimal: True if the solution is optimal
                obj: objective function of the best solution found
                sol: list of the paths of each courier in the best solution
        """
        rho, X, _, dist_courier, _ = variables
        m,n, _,_, D = instance.unpack()

        if strategy == CBC:
            solver = PULP_CBC_CMD(timeLimit=self.timeout - 10, msg=1)
        elif strategy == GLPK:
            solver = GLPK_CMD(timeLimit=self.timeout - 10, msg=1)
        
        solver.msg = False
        self.solver.solutionTime = self.timeout
        start_time = t.time()

        class ElementNotFoundException(Exception):
            pass

        try:
            
            self.solver.solve(solver)
            
            if sub_tour_elimination == "_DFJ" :
                route = [[] for i in range(m)]
                
                for k in range(m):
                    route[k] = [(i,j) for i in range(n+1) \
                        for j in range(n+1) if pulp.value(X[i][j][k]) == 1]

                route_plan = [self.get_plan(route[k]) 
                              for k in range(m)]
                
                #check if subtours are present
                subtour_present = np.array([len(route_plan[k]) > 1 for k in range(m)]).any()
                subtour = [[] for i in range(m)]
                solver_time = int(t.time() - start_time)
                # we add iteratively constraints to eliminate sub tours
                if solver_time >= 300:
                    return  300, False, None , []
                
                while(subtour_present):
                    for k in range(m):
                        while len(route_plan[k]) > 1:  
                            for i in range(len(route_plan[k])):
                                    #the sum of xijk in the sub tour has to be lower than the n. of places in the subtour
                                    self.solver += lpSum(X[route_plan[k][i][j][0]][route_plan[k][i][j][1]][k] \
                                                    for j in range(len(route_plan[k][i]))) <=\
                                                                len(route_plan[k][i]) - 1
                            
                            if solver_time <= self.timeout:                             
                                self.solver.solve(solver)
                            
                            solver_time = int(t.time() - start_time)
                            
                            if solver_time >= self.timeout:
                                return  self.timeout, False, None , []
                            
                            remaining_time = self.timeout - int(t.time() - start_time)
                            solver.timelimit = remaining_time
                            
                                
                            for s in range(m):
                                route[s] = [(i, j) for i in range(n+1) \
                                            for j in range(n+1) 
                                            if X[i][j][s].varValue == 1]
                                
                                route_plan[s] = self.get_plan(route[s])
                            
                            subtour[k].append(len(route_plan[k]))

                    subtour_present = np.array([len(route_plan[k]) > 1 for k in range(m)]).any()
       
            # time = int(self.solver.solutionTime)
            time = np.round(t.time() - start_time,2)
            
            
            if time < self.timeout - 10:
                optimal = True
                time = int(self.solver.solutionTime)
            else:
                optimal = False
                time = self.timeout
            
            
            
            obj = int(rho.varValue)
            
            solution_matrix = np.array([[[int(X[i][j][k].varValue) for k in range(m)]
                            for j in range(n + 1)] for i in range(n + 1)])
            
            dist_cour_mat = [int(dist_courier[k].varValue) for k in range(m)]

            solution = []
            element_present = set()

            for k in range(m):
                route = []
                for i in range(n + 1):
                    for j in range(n + 1):
                        if i != j and solution_matrix[i][j][k] == 1:
                            route.append([i, j])
                solution.append(route)
                
            sol = []
            for k in range(m):
                travel = [n]
                for i in range(len(solution[k])):
                    for j in range(len(solution[k])): 
                                       
                        if solution[k][j][0] == travel[i]:
                            travel.append(solution[k][j][1])
                            element_present.add(solution[k][j][1])
                sol.append(travel) 
            
            for i in range(n+1):
                if i not in element_present:
                    raise ElementNotFoundException(
                        f"Item {i} is not in the solution")

            if self.mode == 'v':

                print("Time needed to solve the instance: ", time,"s.")
                print("Solution:")

                for k in range(m):

                    print("Courier ",k+1, end=": ")
                    for j in range(len(sol[k])-1):
                        if sol[k][j] == n:
                            print("deposit", " => ",end="")
                        else:
                            print(sol[k][j]+1, " => ",end = "")
                    print("deposit")
                print("Distance travelled:")
                for k in range(m):
                    print("Courier",k+1,": ",int(dist_cour_mat[k]))
            
            dist_cour_mat, result = instance.post_process_instance(dist_cour_mat,sol)
            
            result = [[x + 1 for x in sublist if x != n] for sublist in result]
            
            return time , optimal, obj, result
        
        except ElementNotFoundException as e:
            return int(self.timeout), False, None , []
        
    def get_plan(self,r0):
        """
        Creates a list of paths from a list of transitions between nodes in a graph.

        :param r0: List of tuples representing transitions between nodes.
        :return: List of paths-> route.
        """
        r=copy.copy(r0)
        route = []
        while len(r) != 0:
            plan = [r[0]]
            del (r[0])
            l = 0
            while len(plan) > l:
                l = len(plan)
                for i, j in enumerate(r):
                    if plan[-1][1] == j[0]:
                        plan.append(j)
                        del (r[i])
            route.append(plan)
        return(route)
   
    def model1(self,instance,strategy_sub_t = "_mtz"):
        """
        Defines the model and the constraints
        
        """

       
        m,n,s,l,D = instance.unpack()  

        distance_lb = instance.courier_dist_lb

        distance_ub = instance.courier_dist_ub

        rho_lb = instance.rho_low_bound
        
        courier_low_bound = instance.courier_min_load
        
        courier_up_bound = instance.courier_max_load

        #  it's set to 1 if the arc from node i  to node j is in the optimal route and is driven by vehicle k
        X = [[[ LpVariable(name=f'X_{i}_{j}_{k}', lowBound=0, upBound=1, cat=LpBinary) 
               for k in range(m) ] for j in range(n + 1) ] for i in range(n + 1)]
        
        # Load carried by each courier
        load_courier = [LpVariable(name=f'load_cour_{i}', cat=LpInteger ,
                                    lowBound = courier_low_bound, upBound = courier_up_bound) for i in range(m)]

        # Distance travelled by each courier
        dist_courier = [LpVariable(name=f'dist_cour_{i}', cat=LpInteger ,
                                    lowBound = distance_lb, upBound = distance_ub) for i in range(m)]
        
        rho = LpVariable(name=f'rho', 
                             lowBound = rho_lb, upBound = distance_ub , cat = distance_ub)
        
        
        #1. vehicle leaves node that it enters
        for j in range(n + 1):
            for k in range(m):
                self.solver += lpSum([X[i][j][k] 
                                      for i in range(n + 1)]) == lpSum([X[j][i][k] 
                                                                                   for i in range(n + 1)])

        # #2 every node is entered once
        for j in range (n):
            self.solver += lpSum([[X[i][j][k] 
                                   for i in range(n + 1)] for k in range(m)]) == 1

        # # no travel from a node to itself
        for i in range(n + 1):
            for k in range(m):
                self.solver += X[i][i][k] == 0

        #######################################################
        # subtour elimination
        if strategy_sub_t == "_time_order":
            Y = [[LpVariable(name = f"Order_{k}_{i}",lowBound = 0, upBound = n-1) 
                  for i in range(n)] for k in range(m)]
            
            for k in range(m):
                for j in range(n):
                    for i in range(n):
                         self.solver += X[i][j][k]*(n-1) + Y[k][i] - Y[k][j]  <= n-2
                     
        elif strategy_sub_t == "_mtz":
            Y = [[LpVariable(name = f"Order_{k}_{i}",lowBound = 0, upBound = n-1) 
                  for i in range(n)] for k in range(m)]
            
            for k in range(m):
                for i in range(n):
                    for j in range(n):
                        if i!=j :
                            self.solver += Y[k][j]>= Y[k][i] +1 - (2*n)*(1-X[i][j][k])
        elif strategy_sub_t == "_DFJ":
            Y = None 
                           

        ########################################################

        #3 every vehicles leaves the depot
        for k in range(m):
            self.solver+= lpSum(X[n][j][k] for j in range(n)) == 1 
            
        
        #4 load constraint
        for k in range(m):
            self.solver += load_courier[k] == lpSum([s[j]*X[i][j][k] for j in range( n ) 
                                  for i in range(n + 1)]) 
            self.solver += load_courier[k] <= l[k]

        # distance constraint
        for k in range(m): 
            self.solver += dist_courier[k] == lpSum(D[i][j] * X[i][j][k]
                                                    for j in range(n + 1) for i in range(n + 1))

        #7. Goal function. We want to minimize the max distance.
        for i in range(m):
            self.solver += rho >= dist_courier[i] 

        self.solver += rho

        return rho, X, Y, dist_courier, load_courier

    def add_sb_constraint(self,instance,variables):
        """
        Adds symmetry breaking constraints
        
        """ 
        _ , X, _, _, load_courier = variables
        
        m, n, _, _, D = instance.unpack()
         
        for k in range(m-1):
            self.solver += load_courier[k+1] <= load_courier[k]
        # if the distance matrix is symmetric, we have a reflection symmetry between any courier path and its inverse
        if (D == D.T).all():
            print("Symmetric distance matrix")
            for k in range(m):
                for i in range(n):
                    self.solver += X[i][n][k] <= lpSum(X[n][j][k] for j in range(n))

            


    
        