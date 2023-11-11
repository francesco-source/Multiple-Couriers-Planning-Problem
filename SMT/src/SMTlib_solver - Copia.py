import subprocess
import os 
import time as t
from SMT.src.solver import SMTsolver
from SMT.src.SMT_utils import *
from utils import *
from constants import *

class SMTLIBsolver(SMTsolver):
    
    def __init__(self,data,directory, timeout = 300, mode = "v"):
        super().__init__(data,directory=directory,timeout = timeout, mode = mode)
        self.timeout = timeout
        self.output_dir = directory
        self.symmetry = None
        self.file = None
        os.makedirs("SMT/src/instances_smtlib/", exist_ok=True) 
        self.set_solver()
        
        

       
    def init_file(self, instance, strategy = "linear"):
        to_write = "(set-logic ALL)\n" + self.solver.sexpr()
        with open(self.file, "w") as f:
            f.write(to_write)
        self.set_solver() # setting the Solver to create the model
        self.set_constraints(instance= instance, strategy= strategy)
     
     
    def add_instructions(self,instance, bash_file,solver):

        couriers, num_items, item_size, courier_size, distances = instance.unpack()
        courier_dist_ub = instance.courier_dist_ub
        rho_low_bound = instance.rho_low_bound
        courier_dist_lb = instance.courier_dist_lb

        path = os.path.join(os.getcwd(), bash_file)
        instruction = f"timeout {self.timeout} bash file {path} '{self.file}' 'max' '{courier_dist_ub}' '{rho_low_bound-1}' '{solver}' '{couriers}' '{num_items + 1}'"

        return instruction
    
    
    def solve(self):
        self.directory + "/SMTlib/"
        strategy = "linear"
        for num, instance in self.data.items():
            json_dict = {}
            filename = str(num) + ".json"
            for solver, solverstr in SOLVERS_SMTlib.items():
                print("Solver: ", solverstr, "",strategy," search")
                print("INSTANCE N", num)
                for sym, symstr in SYM_DICT.items():
                    bash_file = "SMT/src/" + strategy + ".sh"
                    self.file = s"SMT/src/instances_smtlib/" + str(num).removesuffix('.dat') + ".smt2"
                    self.init_file(instance)
                    
                    bash_instruction = self.add_instructions(instance, bash_file, solverstr)
                    
                    print(bash_instruction) # usciranno 20 camndi uno per istanza
                        
                    print("------- Execution --------")
                    start_time = t.time()
                    # try:
                    result = subprocess.run(bash_instruction, shell= True, capture_output= True, text= True)
                    time = t.time() - start_time
                    print(result)
                    # except Exception as e:
                    #     print("The bash file cannot be executed:", e)
                    #     out_dict = {
                    #         'time': self.timeout,
                    #         'optimal': False,
                    #         'obj': "n/a",
                    #         'sol': []
                    #     }
                        
                    key_dict = solverstr + symstr
                    #json_dict[key_dict] = {"time" : time, "optimal": optimal, "obj": obj, "sol": sol}
                    
        