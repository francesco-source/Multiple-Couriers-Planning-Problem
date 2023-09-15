from pulp import *
import numpy as np
from utils import *
import time
import signal
from MIP.src.mip_utils import *
from constants import *
from datetime import datetime

class MIPsolver:

    def __init__(self, data, output_dir, timeout = 270, mode = 'v'):

        self.data = data
        self.output_dir = output_dir
        self.timeout = timeout
        self.solver = None
        self.mode = mode


    def set_solver(self,name = f"solve_instance",sense = LpMinimize):
        self.solver = LpProblem(name = name, sense = sense)

    
    def solve(self):
        path = self.output_dir + "/MIP/"
        for num, instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for strategy, stratstr in STRATEGIES_MIP_DICT.items():
                for sym , symstr in SYM_DICT.items():
                    self.set_solver()
                    
                    variables = self.model1(instance)
                    
                    if sym == SYMMETRY_BREAKING:
                        self.add_sb_constraint(instance,variables)
                        

                    time, optimal, obj,res = self.optimize(instance,strategy,variables)
                    
                    self.print_obj_dist(obj,sym,stratstr)

                    # create the optimize function in order to  obtain everything you whan
                    key_dict =  stratstr
                    json_dict[key_dict] = {"time" : time, "optimal": optimal, "obj": obj, "sol": res}
                    if self.mode == 'v':
                        print()
                if self.mode == 'v':
                    print()
            print()          

        save_file(path, num + ".json", json_dict)

    def print_obj_dist(self,obj,sym,strastr):
        
            print(f"Max distance found using {strastr} solver,{' without sb :' if sym==NO_SYMMETRY_BREAKING else ''} {obj}")

    
    def optimize(self,instance,strategy,variables):
             
             return self.search(instance,variables,strategy)
         

    
    def search(self,instance,variables,strategy):

        rho, X,Y, dist_courier = variables

        m,n, _,_, D = instance.unpack()

        if strategy == CBC:
            solver = PULP_CBC_CMD(timeLimit=self.timeout, msg=1)
        elif strategy == GLPK:
            solver = GLPK_CMD(timeLimit=self.timeout, msg=1)
        # elif strategy == HIGH:
        #     solver = HiGHS_CMD(timeLimit=self.timeout,msg=1)

        solver.msg = False
        self.solver.solutionTime = self.timeout
        start_time = datetime.now()

        class ElementNotFoundException(Exception):
            pass
        try:
            self.solver.solve(solver)
            end_time = datetime.now()
            interval = end_time - start_time

            print("Time interval needed to solve the model: ", interval)

            optimal = True

            time = int(self.solver.solutionTime)
            
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
                        "The model wasn't able to encode properly",
                        "and solve the problem in the time window.")

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

            print(e)


            return time, False, None , []
   
    def model1(self,instance):

        m,n,s,l,D = instance.unpack()  

        distance_lb = instance.courier_dist_lb

        distance_ub = instance.courier_dist_ub

        rho_lb = instance.rho_low_bound

        #  has a value of 1 if the arc from node to node is in the optimal route and is driven by vehicle k
        X = [[[ LpVariable(name=f'X_{i}_{j}_{k}', lowBound=0, upBound=1, cat=LpBinary) 
               for k in range(m) ] for j in range(n + 1) ] for i in range(n + 1)]
        
        Y = [[LpVariable(name = f"Order_{k}_{i}",lowBound = 0, upBound = n-1) for i in range(n)] for k in range(m)]
        
        # Create the distance variables for each courier
        dist_courier = [LpVariable(name=f'dist_cour_{i}', cat=LpInteger ,
                                    lowBound = distance_lb, upBound=distance_ub) for i in range(m)]
        
        rho = LpVariable(name=f'rho', 
                             lowBound = rho_lb, upBound =distance_ub , cat = distance_ub)
        
        
        #1. vehicle leaves node that it enters
        for j in range(n + 1):
            for k in range(m):
                self.solver += lpSum([X[i][j][k] for i in range(n + 1)]) == lpSum([X[j][i][k] for i in range(n + 1)])


        # #2 every node is entered once
        for j in range (n):
            self.solver += lpSum([[X[i][j][k] for i in range(n + 1)] for k in range(m)]) == 1

        # # no travel from a node to itself
        for i in range(n + 1):
            for k in range(m):
                self.solver += X[i][i][k] == 0


        
        for k in range(m):
            for j in range(n):
                for i in range(n):
                   self.solver += X[i][j][k]*(n-1) + Y[k][j] - Y[k][i]  <= n-2


        #3 every vehicles leaves the depot
        for k in range(m):
            self.solver+= lpSum(X[n][j][k] for j in range(n)) == 1
        
        # #4 load constraint
        for k in range(m):
            self.solver += lpSum([s[j]*X[i][j][k] for j in range( n ) for i in range(n + 1)]) <= l[k]


        # distance constraint
        for k in range(m): 
            self.solver += dist_courier[k] == lpSum(D[i][j] * X[i][j][k] for j in range(n + 1) for i in range(n + 1))

        #7. Goal function. We want to minimize the max distance.
        for i in range(m):
            self.solver += rho >= dist_courier[i] 

        self.solver += rho

        return rho,X,Y,dist_courier

    def add_sb_constraint(self,instance,variables):
        
        rho , X,Y, dist_courier = variables
        
        m, n , _,_, _ = instance.unpack()
        
        # li ha fatti chat gpt non penso abbiano senso. Nessun senso
        for k in range(m):
            for i in range(n):
                for j in range(i + 1, n ):
                     self.solver += Y[k][i] + (n - 1) * X[i][j][k] <= Y[k][j]

        for k in range(m):
            for i in range(n):
                for j in range(i + 1, n):
                    self.solver += Y[k][i] <= Y[k][j]

            


    def add_constraint_2(self,instance):
        m,n,s,l,D = instance.unpack()  
        distance_lb = instance.courier_dist_lb
        distance_ub = instance.courier_dist_ub
        rho_lb = instance.rho_low_bound

        # matrix m*n*n+1 where we have couriers, order and packages
        X  = [[[LpVariable(name = f'X_{i}_{k}_{j}', lowBound = 0, upBound = 1, cat = LpBinary) 
                for j in range(n+1)] for k in range(n)] for i in range(m)]

        #distance made by each courier
        dist_courier = [LpVariable(name = f'dist_cour{i}', cat = LpInteger,lowBound = distance_lb, upBound = distance_ub) 
                        for i in range(m)]

        rho = LpVariable(name=f'maximum', lowBound = rho_lb, upBound =distance_ub , cat = LpInteger)

        #1. One hot encoding 
        for i in range(m):
            for k in range(n):
                self.solver += lpSum([X[i][k][j]for j in range(n+1)]) == 1

        #2. Each element only once in the cube
        for j in range(n):
            self.solver += lpSum([[X[i][k][j] for k in range(n)] for i in range(m)]) == 1

        #3. Load size constraint ( migliora con LpAffineSumExpression)
        for i in range(m):
            self.solver += lpSum([s[j]*X[i][k][j] for j in range(n) for k in range(n)]) <= l[i]
        
        #4. Every courier must start.
        self.solver += lpSum(X[i][0][n] for i in range(m)) == 0

        #5. Constraint that if I see a 0, all the following element for a courier must be 0.
        for i in range(m):
            for k in range(n-1):
                    self.solver += X[i][k][n] - X[i][k+1][n] <= 0 

        # 6. Distances traveled by each courier
        for i in range(m):
            self.solver += dist_courier[i] == lpSum([[X[i][0][j] * D[n][j] for j in range(n)],[
            lpDot([And(self.solver,X[i][j-1][k1],X[i][j][k2],f"{i}carries{k1}to{k2}in{j}") 
                    for j in range(1,n) for k1 in range(n+1) for k2 in range(n+1) if k1!= k2]
                    ,[D[k1][k2] for j in range(n-1) for k1 in range(n+1) for k2 in range(n+1) if k1 != k2])]])

        #7. Goal function. We want to minimize the max distance.
        for i in range(m):
            self.solver += rho >= dist_courier[i] 
            
        self.solver += rho

        return rho, X, dist_courier

        