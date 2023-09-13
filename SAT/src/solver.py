import time as t
from SAT.src.SAT_utils import *
from constants import *
from utils import *

class SATsolver:
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
        path = self.output_dir + "/SAT/"
        
        for num, instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for strategy, stratstr in STRATEGIES_DICT.items():
                for sym, symstr in SYM_DICT.items():
                    self.set_solver()
                    
                    variables = self.set_constraints(instance, strategy)
                    
                    if sym == SYMMETRY_BREAKING:
                        self.add_sb_constraints(instance, variables)
                    
                    time, optimal, obj, sol = self.optimize(instance, strategy, variables)
                    
                    print(f"Max distance found using {stratstr} search{':      ' if sym==NO_SYMMETRY_BREAKING else ' w sb: '}: {obj}")
                    
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
        rho, X, D_tot, _ = variables
        m,n,_,_,D = instance.unpack()
        maxDistBin= int(np.ceil(np.log2(n * np.max(D))))
        
        start_time = t.time()        
        iter = 0
        
        previousModel = None
        satisfiable = True
        optimal = True

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
                
                dist = [model.evaluate(rho[b]) for b in range(maxDistBin)]
                self.solver.add(Not(lesseq(dist, rho)))
                
                
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
        x = [[[ model.evaluate(X[i][j][k]) for k in range(0,n+1) ] for j in range(n) ] for i in range(m)]
        xDD = [[model.evaluate(D_tot[i][b]) for b in range(maxDistBin)] for i in range(m)]
        
        distances = [toInteger(np.array(xDD[i])) for i in range(m)]
        obj = max(distances)
        
        tot_s = []
        for i in range(m):
            sol = []
            for j in range(n):
                for k in range(1,n+1):
                    if x[i][j][k] == True:
                        sol.append(k)
            tot_s.append(sol)

        distances,tot_s = instance.post_process_instance(distances,tot_s)
        
        if self.mode == 'v':
            print("Time from beginning of the computation:", np.round(past_time, 2), "seconds")
            
            print("Solution:")
            for i in range(m):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in tot_s[i]:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i in range(m):
                print(f"Courier {i+1}: ", toInteger(np.array(xDD[i])))
        

        return int(past_time), optimal, obj, tot_s
        
    def binary_search(self, instance, variables):
        rho, X, D_tot, _ = variables
        m,n,_,_,D = instance.unpack()
        maxDistBin= int(np.ceil(np.log2(n * np.max(D))))
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
            if (UPPER_BOUND - LOWER_BOUND) <= 1:
                if self.mode == 'v':
                    print(f"UPPER={UPPER_BOUND}, LOWER= {LOWER_BOUND}: last search")
                satisfiable = False
            
            if UPPER_BOUND - LOWER_BOUND == 1:
                MIDDLE_BOUND = LOWER_BOUND
            else:
                MIDDLE_BOUND = int(np.ceil((UPPER_BOUND + LOWER_BOUND) / 2))
            middle_bits = toBinary(MIDDLE_BOUND, maxDistBin, BoolVal)  # notice the +0
            
            self.solver.add(lesseq(rho, middle_bits))
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
                dist = [model.evaluate(rho[b]) for b in range(maxDistBin)]
                if self.mode == 'v':
                    print(" obj: ", toInteger(dist))
                UPPER_BOUND = toInteger(dist)

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
            
        
        current_time = t.time()
        past_time = current_time - start_time

        model = previousModel
        x = [[[ model.evaluate(X[i][j][k]) for k in range(0,n+1) ] for j in range(n) ] for i in range(m)]
        xDist = [[model.evaluate(D_tot[i][b]) for b in range(maxDistBin)] for i in range(m)]
        distances = [toInteger(np.array(xDist[i])) for i in range(m)]
        obj = max(distances)
        # output  
        tot_s = []
        for i in range(m):
            sol = []
            for j in range(n):
                for k in range(1,n+1):
                    if x[i][j][k] == True:
                        sol.append(k)
            tot_s.append(sol)

        distances,tot_s = instance.post_process_instance(distances,tot_s)
        
        if self.mode == 'v':
            print("Time from beginning of the computation:", np.round(past_time, 2), "seconds")
            print("Solution:")
            for i in range(m):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in tot_s[i]:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i in range(m):
                print(f"Courier {i+1}: ", toInteger(np.array(xDist[i])))

        
        
        

        return int(past_time), optimal, obj, tot_s
    
    
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

        maxs = np.max(instance.s)
        maxl = np.max(instance.l)
        maxD = np.max(instance.D)
        maxDBin = int(np.ceil(np.log2(maxD)))
        maxDist = n * maxD
        maxDistBin = int(np.ceil(np.log2(maxDist)))
        maxWeight = np.sum(instance.s)
        maxWeightBin = int(np.ceil(np.log2(maxWeight)))
        maxDBin = maxDistBin

        X = [[[Bool(f"x_{i}_{j}_{k}") for k in range(0,n+1)] for j in range(n)] for i in range(m)]

        # save the values of the instance
        l = [[BoolVal(b) for b in toBinary(l[i], length= maxWeightBin)] for i in range(m)]
        s = [[BoolVal(b) for b in toBinary(s[j], length= maxWeightBin)] for j in range(n)]
        D = [[[BoolVal(b) for b in toBinary(D[i][j], length= maxDBin)] for j in range(n+1)] for i in range(n+1)]

        # each cell has only one value.
        for i in range(m):
            for j in range(n):
                self.solver.add(exactly_one(X[i][j], f"valid_cell_{i}_{j}"))

        # each element except zero should be seen only once inside the matrix
        for k in range(1,n+1):
            self.solver.add(exactly_one([X[i][j][k] for i in range(m) for j in range(n)],f"valid_k{k}"))

        # ordering constraint: if the courier does not take the kth pack at position j, also at position j+1 doesnt
        for i in range(m):
            for j in range(n-1):
                self.solver.add(Implies(X[i][j][0], X[i][j+1][0]))
        # each courier can only deliver items whose total size doesn't exceed limit
        """
        W_par is a matrix that contains for each courier i= 0..m-1, the binary 
        encoding of the weight of the item k= 0..n ONLY IF it is carried by i,
        0 otherwise
        The weight of each item, or 0 is summed and saved into the matrix W_tot
        """
        W_par = [[[Bool(f"partial_weight_{i}_{k}_{b}") for b in range(maxWeightBin)] for k in range(n)] for i in range(m)]
        W_tot = [[Bool(f"total_weight_{i}_{b}") for b in range(maxWeightBin)] for i in range(m)]

        for i in range(m):
            # 1. copy the weight from s to partial weight if needed
            for k in range(n):
                self.solver.add( Implies( at_least_one([X[i][j][k+1] for j in range(n)]), And([W_par[i][k][b] == s[k][b] for b in range(maxWeightBin)])))
                self.solver.add( Implies( Not(at_least_one([X[i][j][k+1] for j in range(n)])), And([Not(W_par[i][k][b]) for b in range(maxWeightBin)])))
            # 2. compute the sum of the partial weights for each courier
            self.solver.add(sum_vec(W_par[i], W_tot[i], name= f"weight_{i}"))
            # 3. for each courier the sum should be less than or equal to the max load size
            self.solver.add(lesseq(W_tot[i], l[i]))

        D_par = [[[Bool(f"partial_distances_{i}_{j}_{b}") for b in range(maxDBin)] for j in range(n+1)] for i in range(m)]
        D_tot = [[ Bool(f"total_distances_{i}_{b}") for b in range(maxDistBin)] for i in range(m)]
        
        rho = [Bool(f"obj_{b}") for b in range(maxDistBin)]

        # 1. copy the distances from D to partial distances if needed
        for i in range(m):
            # from deposit to first place
            ## sol.add(Implies(X[i][0][0], equals(D_par[i][0], D[n][n])))
            self.solver.add(Implies(X[i][0][0], And([Not(D_par[i][j][b]) for j in range(n+1) for b in range(maxDBin)])))
            
            for k in range(1, n+1):
                self.solver.add(Implies(Not(X[i][0][0]), Implies(X[i][0][k], equals(D_par[i][0], D[n][k-1]))))
            
            # from j - 1 to j
            for j in range(1, n):
                for k1 in range(1, n+1):
                    for k2 in range(1, n+1):
                        self.solver.add(Implies(Not(X[i][0][0]), Implies(And(X[i][j-1][k1], X[i][j][k2]), equals(D_par[i][j], D[k1-1][k2-1]))))     

                    self.solver.add(Implies(Not(X[i][0][0]), Implies(And(X[i][j-1][k1], Not(at_least_one(X[i][j][1:]))), equals(D_par[i][j], D[k1-1][n]))))
                self.solver.add(Implies(Not(X[i][0][0]), Implies(And(X[i][j-1][0], X[i][j][0]), equals(D_par[i][j], D[n][n]))))

            # da  testare in un istanza dove un solo corriere porta tutto!! Fatto
            for k in range(1, n+1):
                self.solver.add(Implies(X[i][-1][k], equals(D_par[i][-1], D[k-1][n])))

            self.solver.add(Implies(X[i][-1][0], equals(D_par[i][-1], D[n][n]))) # se il corriere non porta pacchi nell'istante j allora copia 0 nelle distanze
        
            # 2. compute the sum of the distances for each courier
        # for i in range(m):
            self.solver.add(sum_vec(D_par[i], D_tot[i], name= f"dist_{i}"))
        # 3. --NO save the maximum-- --> rho >= d1...dn
            self.solver.add(lesseq(D_tot[i], rho))

        # search heuristics: only the first couriers (those with the most size) carry the most items
        for i in range(m-1):
            for j in range(n):
                self.solver.add(Implies(X[i][j][0], X[i+1][j][0]))

        return rho, X, D_tot, W_tot
        
    def add_bin_constr(self, instance):
        m, n, s, l, D = instance.unpack()

        maxD = np.max(D)
        maxDBin = int(np.ceil(np.log2(maxD)))
        maxDist = n * maxD
        maxDistBin = int(np.ceil(np.log2(maxDist)))
        maxWeight = np.sum(s)
        maxWeightBin = int(np.ceil(np.log2(maxWeight)))
        maxDBin = maxDistBin

        X = [[[Bool(f"x_{i}_{j}_{k}") for k in range(0,n+1)] for j in range(n)] for i in range(m)]

        # save the values of the instance
        l = [[BoolVal(b) for b in toBinary(l[i], length= maxWeightBin)] for i in range(m)]
        s = [[BoolVal(b) for b in toBinary(s[j], length= maxWeightBin)] for j in range(n)]
        D = [[[BoolVal(b) for b in toBinary(D[i][j], length= maxDBin)] for j in range(n+1)] for i in range(n+1)]

        # each cell has only one value.
        for i in range(m):
            for j in range(n):
                self.solver.add(exactly_one(X[i][j], f"valid_cell_{i}_{j}"))

        # each element except zero should be seen only once inside the matrix
        for k in range(1,n+1):
            self.solver.add(exactly_one([X[i][j][k] for i in range(m) for j in range(n)],f"valid_k{k}"))

        # ordering constraint: if the courier does not take the kth pack at position j, also at position j+1 doesnt
        for i in range(m):
            for j in range(n-1):
                self.solver.add(Implies(X[i][j][0], X[i][j+1][0]))
        # each courier can only deliver items whose total size doesn't exceed limit
        """
        W_par is a matrix that contains for each courier i= 0..m-1, the binary 
        encoding of the weight of the item k= 0..n ONLY IF it is carried by i,
        0 otherwise
        The weight of each item, or 0 is summed and saved into the matrix W_tot
        """
        W_par = [[[Bool(f"partial_weight_{i}_{k}_{b}") for b in range(maxWeightBin)] for k in range(n)] for i in range(m)]
        W_tot = [[Bool(f"total_weight_{i}_{b}") for b in range(maxWeightBin)] for i in range(m)]

        for i in range(m):
            # 1. copy the weight from s to partial weight if needed
            for k in range(n):
                self.solver.add( Implies( at_least_one([X[i][j][k+1] for j in range(n)]), And([W_par[i][k][b] == s[k][b] for b in range(maxWeightBin)])))
                self.solver.add( Implies( Not(at_least_one([X[i][j][k+1] for j in range(n)])), And([Not(W_par[i][k][b]) for b in range(maxWeightBin)])))
            # 2. compute the sum of the partial weights for each courier
            self.solver.add(sum_vec(W_par[i], W_tot[i], name= f"weight_{i}"))
            # 3. for each courier the sum should be less than or equal to the max load size
            self.solver.add(lesseq(W_tot[i], l[i]))

        D_par = [[[Bool(f"partial_distances_{i}_{j}_{b}") for b in range(maxDBin)] for j in range(n+1)] for i in range(m)]
        D_tot = [[ Bool(f"total_distances_{i}_{b}") for b in range(maxDistBin)] for i in range(m)]
        
        rho = [Bool(f"obj_{b}") for b in range(maxDistBin)]

        # 1. copy the distances from D to partial distances if needed
        for i in range(m):
            # from deposit to first place
            ## sol.add(Implies(X[i][0][0], equals(D_par[i][0], D[n][n])))
            self.solver.add(Implies(X[i][0][0], And([Not(D_par[i][j][b]) for j in range(n+1) for b in range(maxDBin)])))
            
            for k in range(1, n+1):
                self.solver.add(Implies(Not(X[i][0][0]), Implies(X[i][0][k], equals(D_par[i][0], D[n][k-1]))))
            
            # from j - 1 to j
            for j in range(1, n):
                for k1 in range(1, n+1):
                    for k2 in range(1, n+1):
                        self.solver.add(Implies(Not(X[i][0][0]), Implies(And(X[i][j-1][k1], X[i][j][k2]), equals(D_par[i][j], D[k1-1][k2-1]))))     

                    self.solver.add(Implies(Not(X[i][0][0]), Implies(And(X[i][j-1][k1], Not(at_least_one(X[i][j][1:]))), equals(D_par[i][j], D[k1-1][n]))))
                self.solver.add(Implies(Not(X[i][0][0]), Implies(And(X[i][j-1][0], X[i][j][0]), equals(D_par[i][j], D[n][n]))))

            # da  testare in un istanza dove un solo corriere porta tutto!! Fatto
            for k in range(1, n+1):
                self.solver.add(Implies(X[i][-1][k], equals(D_par[i][-1], D[k-1][n])))

            self.solver.add(Implies(X[i][-1][0], equals(D_par[i][-1], D[n][n]))) # se il corriere non porta pacchi nell'istante j allora copia 0 nelle distanze
        
            # 2. compute the sum of the distances for each courier
        # for i in range(m):
            self.solver.add(sum_vec(D_par[i], D_tot[i], name= f"dist_{i}"))
        # 3. save the maximum
        self.solver.add(maximum(D_tot,rho))

        # search heuristics: only the first couriers (those with the most size) carry the most items
        for i in range(m-1):
            for j in range(n):
                self.solver.add(Implies(X[i][j][0], X[i+1][j][0]))

        self.solver.push()
        
        return rho, X, D_tot, W_tot

    def add_sb_constraints(self, instance, variables):
        m, n, s, l, D = instance.unpack()
        _, X, _, W_tot = variables
        # lexicographic ordering between the paths of two couriers with same load capacity
        # se un corriere ha più capacity lo forziamo a depositare più carico
        for i in range(m - 1):
            if l[i] == l[i+1]:
                self.solver.add(ohe_less(X[i][0], X[i+1][0]))
            else: # l[i] > l[i+1]
                self.solver.add(lesseq(W_tot[i+1], W_tot[i]))