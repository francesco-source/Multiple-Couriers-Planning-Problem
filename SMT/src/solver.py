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
        path = self.output_dir + "/SMT/"
        
        for num, instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for strategy, stratstr in STRATEGIES_DICT.items():
                for sym, symstr in SYM_DICT.items():
                    self.set_solver()
                    
                    variables = self.set_constraints(instance, strategy)
                    
                    if sym == SYMMETRY_BREAKING:
                        self.add_sb_constraints(instance)
                    
                    time, optimal, obj, sol = self.optimize(instance, strategy, variables)
                    
                    print(f"Max distance found using {stratstr} search {('' if sym == NO_SYMMETRY_BREAKING else 'w sb')}: {obj}")
                    
                    key_dict = stratstr + symstr
                    json_dict[key_dict] = {"time" : time, "optimal": optimal, "obj": obj, "sol": sol}
                    if self.mode == 'v':
                        print()
                if self.mode == 'v':
                    print()
            print()        

            save_file(path, num + ".json", json_dict)
        
    
    def optimize(self, instance, strategy, variables):   
        
        if strategy == LINEAR_SEARCH:
            time, optimal, obj, sol = self.linear_search(instance, variables)
        elif strategy == BINARY_SEARCH:
            time, optimal, obj, sol = self.binary_search(instance, variables)
        
        return time, optimal, obj, sol
    
    def linear_search(self, instance, variables):
        rho, x, m_dist = variables
        m,n,_,_,_ = instance.unpack()        
        
        start_time = t.time()        
        iter = 0
  
        satisfiable = True
        optimal = True
        previousModel = None

        self.solver.push()
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
                    return past_time, False, "N/A", "N/A"
                satisfiable = False

            elif status == unknown:
                if iter == 0:
                    print("UNKNOWN RESULT for insufficient time")
                    return self.timeout, False, "N/A", "N/A"
                satisfiable = False
                optimal = False
                
        current_time = t.time()
        past_time = int((current_time - start_time))

        model = previousModel
        sol = [[int(str(model.evaluate(x[k][j]))) for j in range(n + 1) if int(str(model.evaluate(x[k][j]))) != n+1] for k in range(m)]
        distances = [int(str(model.evaluate(m_dist[i]))) for i in range(m)]
        obj = max(distances)

        if self.mode == 'v':
            if past_time >= 300:
                print(f"The computation time exceeded the limit ({self.timeout} seconds)")
            else: print("Time from beginning of the computation:", past_time, "seconds")
            
            print("Solution:")
            for i in range(m):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in sol[i]:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i in range(m):
                print(f"Courier {i+1}: ", distances[i])

        return past_time, optimal, obj, sol
    
    def binary_search(self, instance, variables):
        rho, x, m_dist = variables
        m,n,_,_,D = instance.unpack()        
        
        maxDist = n * np.max(D)
        
        UPPER_BOUND = maxDist
        LOWER_BOUND = np.max(D[-1] + D[:,-1])
        
        self.solver.set('timeout', self.timeout * 1000)

        start_time = t.time()
        iter = 0
        
        satisfiable = True
        optimal = True
        previousModel = None
        
        while(satisfiable):
            if (int(str(UPPER_BOUND)) - int(str(LOWER_BOUND))) <= 1:
                if self.mode == 'v':
                    print(f"UPPER={UPPER_BOUND}, LOWER= {LOWER_BOUND}: last search")
                satisfiable = False
            
            if int(str(UPPER_BOUND)) - int(str(LOWER_BOUND)) == 1:
                MIDDLE_BOUND = LOWER_BOUND
            else:
                MIDDLE_BOUND = int(np.ceil((int(str(UPPER_BOUND)) + int(str(LOWER_BOUND))) / 2))
            
            self.solver.add(rho <= MIDDLE_BOUND)
            
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
                    return past_time, False, "N/A", "N/A"
                iter += 1
                self.solver.pop()
                self.solver.push()
                LOWER_BOUND = MIDDLE_BOUND
            
            elif status == unknown:
                if iter == 0:
                    print("UNKNOWN RESULT for insufficient time")
                    return self.timeout, False, "N/A", "N/A"
                elif self.mode == 'v':
                    print(f"The computation time exceeded the limit ({self.timeout} seconds)")      
                satisfiable = False
                optimal = False
            
        current_time = t.time()
        past_time = int((current_time - start_time))

        model = previousModel
        sol = [[int(str(model.evaluate(x[k][j]))) for j in range(n + 1) if int(str(model.evaluate(x[k][j]))) != n+1] for k in range(m)]
        distances = [int(str(model.evaluate(m_dist[i]))) for i in range(m)]
        obj = max(distances)

        if self.mode == 'v':
            print("Time from beginning of the computation:", past_time, "seconds")
            
            print("Solution:")
            for i in range(m):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in sol[i]:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i in range(m):
                print(f"Courier {i+1}: ", distances[i])
                
        return past_time, optimal, obj, sol
                
    
    def set_constraints(self, instance, strategy):
        start_time = t.time()
        
        if strategy == LINEAR_SEARCH:
            vars = self.add_lin_constr(instance)
        elif strategy == BINARY_SEARCH:
            vars = self.add_bin_constr(instance)
            
        if self.mode == 'v':
            print("Time needed to encode the instance:", np.round(t.time() - start_time, 2), "seconds")
        return vars
    
    
    def add_lin_constr(self, instance):
        m, n, s, l, D = instance.unpack()
        up_bound = n * np.max(D)
        d_low_bound = np.max(D[-1] + D[:,-1])
        
        couriers_loads = [Int(f'loads{i}') for i in range(m)]
        m_dist = [Int(f"dist{i}") for i in range(m)]
        x = [Array(f"asg{i}", IntSort(), IntSort()) for i in range(m)]

        # maximum = Int(f"max")
        
        # define the domain of x
        for k in range(m):
            for i in range(n + 1):
                self.solver.add(x[k][i] >= 1)
                self.solver.add(x[k][i] <= n+1)
                    
        # # define the domain of maximum
        # solver.add(maximum >= low_bound)
        # self.solver.add(maximum <= up_bound)
        
        # define the domain for m_dist
        for k in range(m):
                self.solver.add(m_dist[k] >= d_low_bound)
                self.solver.add(m_dist[k] <= up_bound)

        # If I go back to the deposit, I'll be in the deposit in all sequent time steps
        for k in range(m):
            for i in range(n+1):
                self.solver.add(Implies(x[k][i] == n+1, And([x[k][j] == n+1 for j in range(i+1, n+1)])))
        
        # Each item must be visited exactly once
        for j in range(1,n + 1):
            self.solver.add(exactly_one([x[k][i] == j for k in range(m) for i in range(n + 1)], f"A{j}"))
                
        # Bin packing capacity
        #for k in range(courier):
                #solver.add(couriers_loads[k] == Sum([If(x[k][i] != items+1, item_size[x[k][i]], 0) for i in range(items+1)]))
        for k in range(m):
            self.solver.add(couriers_loads[k] == Sum([If(x[k][i] == c, s[c-1], 0) for i in range(n+1) for c in range(1,n+1)])) 

        for k in range(m):
            self.solver.add(couriers_loads[k] <= l[k])


        # Compute the distances
        #for k in range(courier):
                #solver.add(m_dist[k] == Sum(array_of_distances[items][x[k][0]],
                                        #[array_of_distances[x[k][i]][x[k][i+1]] for i in range(1, items)]))
        for k in range(m):
            deposit_distance = [If(x[k][0] == c, int(D[n][c-1]), 0)for c in range(1, n + 2)]
            
            inner_sum = [Sum([If(And(x[k][i] == d, x[k][i+1] == e), int(D[d-1][e-1]), 0) for d in range(1, n + 2) for e in range(1, n + 2)]) for i in range(0, n)]
            total = deposit_distance + inner_sum

            self.solver.add(m_dist[k] == Sum(total))


        # SIMMETRY BREAKING? ORDINE DECRESCENTE DI COURIER_SIZE -> ORDINE DECRESCENTE DI COURIER_LOAD
        
        rho = Int("rho")
        for k in range(m):
            self.solver.add(rho >= m_dist[k])
            
        return rho, x, m_dist
    
    def add_bin_constr(self, instance):
        m, n, s, l, D = instance.unpack()
        up_bound = n * np.max(D)
        low_bound = np.max(D[-1] + D[:,-1])
        
        couriers_loads = [Int(f'loads{i}') for i in range(m)]
        m_dist = [Int(f"dist{i}") for i in range(m)]
        x = [Array(f"asg{i}", IntSort(), IntSort()) for i in range(m)]
        
        rho = Int(f"max")

        # define the domain of x
        for k in range(m):
                for i in range(n + 1):
                    self.solver.add(x[k][i] >= 1)
                    self.solver.add(x[k][i] <= n+1)

        # define the domain of rho
        self.solver.add(rho >= low_bound)
        self.solver.add(rho <= up_bound)

        # # define the domain for m_dist
        # for k in range(m):
        #         self.solver.add(m_dist[k] >= d_low_bound)
        #         self.solver.add(m_dist[k] <= up_bound)

        # # maximum always grater than m_dist
        # for k in range(m):
        #         self.solver.add(rho >= m_dist[k])

        # dopo lo zero son tutti zeri
        for k in range(m):
                for i in range(n+1):
                    self.solver.add(Implies(x[k][i] == n+1, And([x[k][j] == n+1 for j in range(i+1, n+1)])))


        # Each item must be visited exactly once
        for j in range(1,n + 1):
                self.solver.add(exactly_one([x[k][i] == j for k in range(m) for i in range(n + 1)], f"A{j}"))

        # Bin packing capacity
        #for k in range(courier):
                #solver.add(couriers_loads[k] == Sum([If(x[k][i] != items+1, item_size[x[k][i]], 0) for i in range(items+1)]))
        for k in range(m):
                self.solver.add(couriers_loads[k] ==
                        Sum([If(x[k][i] == c, s[c-1], 0) for i in range(n+1) for c in range(1,n+1)]))
        
        #SImmetry breaking constraint
        for k in range(m):
                self.solver.add(couriers_loads[k] <= l[k])

        for k in range(m):
            self.solver.add(x[k][0] != n+1)

        for i in range(m-1):
            for j in range(1,n+1):
                self.solver.add(Implies(x[i][j]==n+1,x[i+1][j]==n+1))

        for k in range(m):
                terms = [
                    If(x[k][0] == c, int(D[n][c-1]), 0) for c in range(1,n+2)
                ] + [
                    If(And(x[k][i] == d, x[k][i+1] == e), int(D[d-1][e-1]), 0)
                    for d in range(1, n + 2) for e in range(1, n + 2) for i in range(n)
                ]

                self.solver.add(m_dist[k] == Sum(terms))

        # Constrain the maximum to be the maximum distance travelled among couriers
        dist = [m_dist[i] for i in range(m)]
        max = dist[0]
        for d in dist[1:]:
            max = If(d > max, d, max)
        self.solver.add(rho == max)

        self.solver.push()

        return rho, x, m_dist