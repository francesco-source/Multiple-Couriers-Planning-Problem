import minizinc as mzn
from constants import *
import datetime as t
from utils import *
import time as tempo

class CPsolver:
    def __init__(self, data, output_dir, timeout=300, mode = 'v'):
        self.data = data
        self.output_dir = output_dir
        self.timeout = timeout
        self.solver = None
        self.mode = mode
        self.solver_path = "./CP/src/"
        self.total_time = tempo.time()


    def solve(self):
        path = self.output_dir + "/CP/"
        for num, mcp_instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for solver_const,solver_name in SOLVERS_CP.items():
                if solver_name != "gecode_heu":
                    self.solver = mzn.Solver.lookup(solver_name)
                else:
                    self.solver = mzn.Solver.lookup("gecode")
                for sym, symstr in SYM_DICT.items():
                        model = mzn.Model(self.solver_path + "model_final" + symstr + ".mzn") 
                        if solver_const == GECODE_HEU:
                            model = mzn.Model(self.solver_path + "model_final_heu" + symstr  + ".mzn")
                          
                        try:
                            
                            mzn_instance = mzn.Instance(self.solver, model)
                            start_time = tempo.time()
                            result = self.search(mcp_instance, mzn_instance,solver_const)
                            end_time = tempo.time()
                            
                            self.total_time = end_time - start_time 
                            
                            if result.status is mzn.Status.UNSATISFIABLE:
                                output_dict = {
                                    'time': int(result.statistics['solveTime'].total_seconds()), 
                                    'optimal': False, 
                                    'obj': "N/A", 
                                    'sol': []
                                    }
                                print("UNSAT")
                            elif result.status is mzn.Status.UNKNOWN:
                                output_dict = {
                                    'time': self.timeout, 
                                    'optimal': False, 
                                    'obj': "N/A", 
                                    'sol': []
                                    }
                                print(f"Insufficient time for {solver_name} solver to compute a solution")
                            else:
                                optimal_path = result["path"] 
                                obj = result["rho"]
                                distances = result["incremental_dist"] [mcp_instance.m + mcp_instance.n:]
                                if self.total_time < self.timeout:
                                    
                                    optimal = True
                                    time = result.statistics['solveTime'].total_seconds() 
                                else:
                                    optimal = False
                                    time = self.timeout
                                    

                                sol = self.get_solution(mcp_instance, optimal_path)

                                distances,sol = mcp_instance.post_process_instance(distances,sol)

                                output_dict = {
                                    'time': int(time), 
                                    'optimal': optimal, 
                                    'obj': obj, 
                                    'sol': sol
                                    }
                                
                                self.print_solution(sol, distances, time)

                                key_dict = solver_name + symstr 
                                json_dict[key_dict] = output_dict
                                if sym == SYMMETRY_BREAKING: 
                                    print("Distance obtained using symmetry breaking")
                                if solver_const == GECODE_HEU:
                                    print(f"Max distance found using: {solver_name} solver with heu: {obj}")
                                else:
                                    print(f"Max distance found using: {solver_name} solver:      {obj}")
                        except Exception as e:
                            print("Exception:", e)
                            output_dict = {
                                        'time': self.timeout,
                                        'optimal': False,
                                        'obj': "N/A",
                                        'sol': []
                                }
                        if self.mode == 'v':
                            print()
                if self.mode == 'v':
                    print()
            print()

            save_file(path, num + ".json", json_dict)


    def search(self, mcp_instance, mzn_instance,solver_const):
        m, n, s, l, D = mcp_instance.unpack()

        mzn_instance["couriers"] = m
        mzn_instance["items"] = n
        mzn_instance["courier_capacity"] = l
        mzn_instance["item_size"] = s
        mzn_instance["distances"] = D
        mzn_instance["sym"] = int(np.array_equal(D, D.T))
        mzn_instance["up_bound"] = mcp_instance.courier_dist_ub
        mzn_instance["low_bound"] = mcp_instance.rho_low_bound
        
        if solver_const == CHUFFED:
            return mzn_instance.solve(timeout=t.timedelta(seconds=self.timeout), \
                                   random_seed=42)
        elif solver_const == GECODE or  solver_const == GECODE_HEU:
            return mzn_instance.solve(timeout=t.timedelta(seconds=self.timeout), \
                                  processes = 10, random_seed=42, free_search=True)
        elif solver_const == HIGHS:
            return mzn_instance.solve(timeout=t.timedelta(seconds=self.timeout), \
                                  processes = 10, random_seed=42)
        elif solver_const == LCG:
            return mzn_instance.solve(timeout=t.timedelta(seconds=self.timeout), \
                                  random_seed=42)
        
        
            
    
    def get_solution(self, inst, path):
        sol = []
        for i in range(inst.m):
            i = path[inst.n + i]-1
            i_path = []
            while i < inst.n+1:
                i_path.append(i+1)
                i = path[i]-1
            sol.append(i_path)
        #print(path, sol, sep= "\n")
        return sol


    def print_solution(self, sol, distances, time= None):
        if self.mode == 'v':
            if time:
                print("Time from beginning of the computation:", np.round(time, 2), "seconds")
            print("Solution:")
            for i, courier_path in enumerate(sol):
                print(f"Courier {i+1}:","deposit => ", end = "")
                for s in courier_path:
                    print(s,"=> ", end = "")
                print("deposit")
            print("Distance travelled:")
            for i, dist in enumerate(distances):
                print(f"Courier {i+1}: ", dist)

