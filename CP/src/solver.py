import minizinc as mzn
from constants import *
import datetime as t
from utils import *

class CPsolver:
    def __init__(self, data, output_dir, timeout=300, mode = 'v'):
        self.data = data
        self.output_dir = output_dir
        self.timeout = timeout
        self.solver = None
        self.mode = mode
        self.solver_path = "./CP/src/"


    def solve(self):
        path = self.output_dir + "/CP/"
        for num, mcp_instance in self.data.items():
            json_dict = {}
            print(f"=================INSTANCE {num}=================")
            for solver_name in SOLVERS_CP:
                self.solver = mzn.Solver.lookup(solver_name)
                for sym, symstr in SYM_DICT.items():
                    model = mzn.Model(self.solver_path + "model" + symstr + ".mzn")

                    try:
                        mzn_instance = mzn.Instance(self.solver, model)
                        result = self.search(mcp_instance, mzn_instance)
                        
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
                            assignments = result["x"]
                            obj = result["rho"]
                            distances = result["m_dist"]

                            if result.status is mzn.Status.OPTIMAL_SOLUTION:
                                optimal = True
                                time = result.statistics['solveTime'].total_seconds()
                            else:
                                optimal = False
                                time = self.timeout

                            sol = [[x for x in sublist if x != mcp_instance.n+1] for sublist in assignments]
                            
                            distances,sol = mcp_instance.post_process_instance(distances,sol)
                            
                            # postprocessing: sia sol sia distances vanno riordinate

                            output_dict = {
                                'time': int(time), 
                                'optimal': optimal, 
                                'obj': obj, 
                                'sol': sol
                                }
                            
                            self.print_solution(sol, distances, time)

                            key_dict = solver_name + symstr
                            json_dict[key_dict] = output_dict
                            
                            print(f"Max distance found using {solver_name} solver{':      ' if sym==NO_SYMMETRY_BREAKING else ' w sb: '}{obj}")
                    
                    ### non capisco perchè serva
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


    def search(self, mcp_instance, mzn_instance):
        m, n, s, l, D = mcp_instance.unpack()

        mzn_instance["courier"] = m
        mzn_instance["items"] = n
        mzn_instance["courier_size"] = l
        mzn_instance["item_size"] = s
        mzn_instance["distances"] = D
        mzn_instance["min_load"] = mcp_instance.courier_min_load
        mzn_instance["max_load"] = mcp_instance.courier_max_load
        mzn_instance["up_bound"] = mcp_instance.courier_dist_ub
        mzn_instance["low_bound"] = mcp_instance.rho_low_bound
        mzn_instance["d_low_bound"] = mcp_instance.courier_dist_lb
        mzn_instance["ratio_packages"] = mcp_instance.ratio_courier_loads
        
        return mzn_instance.solve(timeout=t.timedelta(seconds=self.timeout), \
                                  processes=10, random_seed=42, free_search=True)
    
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