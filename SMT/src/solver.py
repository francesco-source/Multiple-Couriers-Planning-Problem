import time as t
from SMT.src.SMT_utils import *
from constants import *
from utils import *

class SMTsolver:
    def __init__(self, data, output_dir, timeout=300, mode = 'v'):
        self.data = data
        self.output_dir = output_dir
        self.timeout = timeout
        self.solver = Solver()
        self.mode = mode
    
    def set_solver(self):
        self.solver = Solver()
        self.solver.set('timeout', self.timeout * 1000)
    
    def solve(self):
        """
            Runs the solver and saves the results:
                - for each data instance
                - for each solving strategy option
                - for each symmetry breaking option
        """
        path = self.output_dir + "/SMT/"
        
        for num, instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for strategy, stratstr in STRATEGIES_DICT.items():
                for sym, symstr in SYM_DICT_SAT.items():
                    self.set_solver()
                    
                    variables = self.set_constraints(instance, strategy)
                    
                    if sym == SYMMETRY_BREAKING:
                        self.add_sb_constraints(instance, variables)
                        
                    if sym == HEURISTICS:
                        self.add_heu_constraints(instance, variables)
                    
                    time, optimal, obj, sol = self.optimize(instance, strategy, variables)
                    
                    print(f"Max distance found using {stratstr} search", end= "")
                    if sym==NO_SYMMETRY_BREAKING: print(' :      ', end= "")
                    elif sym==SYMMETRY_BREAKING:  print('  w sb: ', end= "")
                    else:                         print(' no heu:', end= "")
                    print(obj)
                    
                    key_dict = stratstr + symstr
                    json_dict[key_dict] = {"time" : time, "optimal": optimal, "obj": obj, "sol": sol}
                    if self.mode == 'v':
                        print()
                if self.mode == 'v':
                    print()
            print()        

            save_file(path, num + ".json", json_dict)
        
    
    def optimize(self, instance, strategy, variables):
        """
            Calls the search functions depending on the strategy selected.
            :return
                time: time needed to solve the instance
                optimal: True if the solution is optimal
                obj: objective function of the best solution found
                sol: list of the paths of each courier in the best solution
        """   
        if strategy == LINEAR_SEARCH:
            time, optimal, obj, sol = self.linear_search(instance, variables)
        elif strategy == BINARY_SEARCH:
            time, optimal, obj, sol = self.binary_search(instance, variables)
        
        return time, optimal, obj, sol
    
    def linear_search(self, instance, variables):
        """
            Runs linear search
            :return
                time: time needed to solve the instance
                optimal: True if the solution is optimal
                obj: objective function of the best solution found
                sol: list of the paths of each courier in the best solution
        """
        rho, x, m_dist, _ = variables
        m,n,_,_,_ = instance.unpack()        
        
        start_time = t.time()        
        iter = 0
  
        satisfiable = True
        optimal = True
        previousModel = None

        self.solver.push()
        #search for a statifiable solution
        while(satisfiable):
            status = self.solver.check()
            if status == sat:
                iter += 1
                model = self.solver.model()
                previousModel = model
            
                current_time = t.time()
            
                past_time = int((current_time - start_time))
                self.solver.set('timeout', (self.timeout - past_time)*1000)
                
                dist = model.evaluate(rho)
                self.solver.add(rho < dist)
                
                
            elif status == unsat:
                if iter == 0:
                    print("UNSAT")
                    past_time = int((current_time - start_time))
                    return past_time, False, "N/A", []
                satisfiable = False

            elif status == unknown:
                if iter == 0:
                    print("UNKNOWN RESULT for insufficient time")
                    return self.timeout, False, "N/A", []
                elif self.mode == 'v':
                    print(f"The computation time exceeded the limit ({self.timeout} seconds)")
                satisfiable = False
                optimal = False
                
        current_time = t.time()
        past_time = current_time - start_time

        model = previousModel
        sol = [[int(str(model.evaluate(x[k][j]))) for j in range(n + 1) if int(str(model.evaluate(x[k][j]))) != n+1] for k in range(m)]
        distances = [int(str(model.evaluate(m_dist[i]))) for i in range(m)]
        obj = max(distances)
        
        distances,sol = instance.post_process_instance(distances,sol)
        
        if self.mode == 'v':
            print("Time from beginning of the computation:", np.round(past_time, 2), "seconds")
            
            print("Solution:")
            for i in range(m):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in sol[i]:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i in range(m):
                print(f"Courier {i+1}: ", distances[i])

        return int(past_time), optimal, obj, sol
    
    def binary_search(self, instance, variables):
        """
            Runs binary search
            :return
                time: time needed to solve the instance
                optimal: True if the solution is optimal
                obj: objective function of the best solution found
                sol: list of the paths of each courier in the best solution
        """
        rho, x, m_dist, _ = variables
        m,n,_,_,D = instance.unpack()        
        
        UPPER_BOUND = instance.courier_dist_ub
        LOWER_BOUND = instance.rho_low_bound
        MIDDLE_BOUND = UPPER_BOUND
        
        self.solver.set('timeout', self.timeout * 1000)

        start_time = t.time()
        iter = 0
        
        satisfiable = True
        optimal = True
        previousModel = None
        
        while(satisfiable):
            
            if self.mode == 'v':
                print(f"search inside [{LOWER_BOUND}-{MIDDLE_BOUND}]: ", end= "")    
            
            current_time = t.time()
            past_time = int(current_time - start_time)
            self.solver.set('timeout', (self.timeout - past_time)*1000)
            
            status = self.solver.check()
            
            if self.mode == 'v':
                print(status, end= ("" if status == sat else "\n"))
                
            if status == sat:
                iter += 1
                model = self.solver.model()
                previousModel = model
                UPPER_BOUND = model.evaluate(rho)
                if self.mode == 'v':
                    print(" obj: ", UPPER_BOUND)

            elif status == unsat:
                if iter == 0:
                    print("UNSAT")
                    past_time = int((current_time - start_time))
                    return past_time, False, "N/A", []
                iter += 1
                self.solver.pop()
                self.solver.push()
                LOWER_BOUND = MIDDLE_BOUND
            
            elif status == unknown:
                if iter == 0:
                    print("UNKNOWN RESULT for insufficient time")
                    return self.timeout, False, "N/A", []
                elif self.mode == 'v':
                    print(f"The computation time exceeded the limit ({self.timeout} seconds)")      
                satisfiable = False
                optimal = False
            
            if (int(str(UPPER_BOUND)) - int(str(LOWER_BOUND))) <= 1: #why not strictly <?
                if self.mode == 'v':
                    print(f"UPPER={UPPER_BOUND}, LOWER= {LOWER_BOUND}: last search")
                satisfiable = False
            
            if int(str(UPPER_BOUND)) - int(str(LOWER_BOUND)) == 1:
                MIDDLE_BOUND = LOWER_BOUND
            else:
                MIDDLE_BOUND = int(np.ceil((int(str(UPPER_BOUND)) + int(str(LOWER_BOUND))) / 2))
            
            self.solver.add(rho <= MIDDLE_BOUND)
            
        current_time = t.time()
        past_time = current_time - start_time

        model = previousModel
        sol = [[int(str(model.evaluate(x[k][j]))) for j in range(n + 1) if int(str(model.evaluate(x[k][j]))) != n+1] for k in range(m)]
        distances = [int(str(model.evaluate(m_dist[i]))) for i in range(m)]
        obj = max(distances)
        
        distances, sol = instance.post_process_instance(distances,sol)

        if self.mode == 'v':
            print("Time from beginning of the computation:", np.round(past_time, 2), "seconds")
            print("Solution:")
            for i in range(m):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in sol[i]:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i in range(m):
                print(f"Courier {i+1}: ", distances[i])
                
        return int(past_time), optimal, obj, sol
                
    
    def set_constraints(self, instance, strategy):
        """
            Adds constraints to the solver and pushes them
        """
        m, n, s, l, D = instance.unpack()
        
        couriers_loads = [Int(f'loads{i}') for i in range(m)]
        m_dist = [Int(f"dist{i}") for i in range(m)]
        x = [Array(f"asg{i}", IntSort(), IntSort()) for i in range(m)]
        rho = Int("obj")
        
        # define the domain of x
        for k in range(m):
            for i in range(n + 1):
                self.solver.add(x[k][i] >= 1)
                self.solver.add(x[k][i] <= n+1)
        
        
        # If I go back to the deposit, I'll be in the deposit in all sequent time steps
        for k in range(m):
            for i in range(n): #n+1
                self.solver.add(Implies(x[k][i] == n+1, And([x[k][j] == n+1 for j in range(i+1, n+1)])))
                
        # Each item must be visited exactly once
        for j in range(1,n + 1):
            self.solver.add(exactly_one([x[k][i] == j for k in range(m) for i in range(n + 1)], f"A{j}"))
        
        # Bin packing capacity
        for k in range(m):
            self.solver.add(couriers_loads[k] == Sum([If(x[k][i] == c, s[c-1], 0) for i in range(n+1) for c in range(1,n+1)])) 
        for k in range(m):
            self.solver.add(couriers_loads[k] <= l[k])
            
        # Compute the distance travelled by each courier
        for k in range(m):
                terms = [
                    If(x[k][0] == c, int(D[n][c-1]), 0) for c in range(1,n+2)
                ] + [
                    If(And(x[k][i] == d, x[k][i+1] == e), int(D[d-1][e-1]), 0)
                    for d in range(1, n + 2) for e in range(1, n + 2) for i in range(n-1)
                ] + [If(x[k][n] == c, int(D[c-1][n]), 0)for c in range(1, n + 2)]

                self.solver.add(m_dist[k] == Sum(terms))
        
        # Each courier must start from the deposit
        for k in range(m):
            self.solver.add(x[k][0] != n+1)   
    
        
        
        if strategy == LINEAR_SEARCH:
            for i in range(m):
                self.solver.add(rho >= m_dist[i])
                
        elif strategy == BINARY_SEARCH:
            dist = [m_dist[i] for i in range(m)]
            max = dist[0]
            for d in dist[1:]:
                max = If(d > max, d, max)
            self.solver.add(rho == max)
            
        
        self.solver.push()
        return rho, x, m_dist, couriers_loads
        

    def add_sb_constraints(self, instance, variables):
        m, n, s, l, D = instance.unpack()
        _, x, _, couriers_loads = variables
        # lexicographic ordering between the paths of two couriers with same load capacity
        # we force a courier with the more capacity to carry the more weight
        for i in range(m-1):
            if l[i] == l[i+1]:
                self.solver.add(x[i][0] <= x[i+1][0]) 
            else: # l[i] > l[i+1]
                self.solver.add(couriers_loads[i+1] <= couriers_loads[i])
        
        self.solver.push()
        
    def add_heu_constraints(self, instance, variables):
        """
            Inserts additional heuristic constraints to the solver and pushes them
        """
        m, n, _, _, _ = instance.unpack()
        _, x, _, _ = variables

        # If a courier i goes to the deposit after j_th item, then also courier i+1 goes to the deposit after j_th item
        for i in range(m-1):
            for j in range(n+1):
                self.solver.add(Implies(x[i][j]==n+1,x[i+1][j]==n+1))
        
        self.solver.push()
