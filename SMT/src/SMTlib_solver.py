import subprocess
import os 
import time as t
from SMT.src.solver import SMTsolver
from SMT.src.SMT_utils import *
from utils import *
from constants import *

class SMTLIBsolver(SMTsolver):
    
    def __init__(self,data,output_dir, timeout = 300, mode = "v"):
        super().__init__(data,output_dir=output_dir,timeout = timeout, mode = mode)
        self.set_solver()
        self.instances_dir = "smt/src/instances_smtlib/"
        os.makedirs(self.instances_dir, exist_ok=True) # creating the dir of smtlib file if exists
        self.output_dir = output_dir
        self.timeout = timeout
        self.set_solver()
        self.symmetry = None
        self.file = None
    
     
        
       
    def create_file(self, instance, strategy = "linear"):
        # smtlib instruction to suppress warning for using different solvers
        self.set_solver() # setting the Solver to create the model
        self.set_constraints(instance= instance, strategy= strategy)
        to_write = "(set-logic ALL)\n" 
        to_write += self.solver.sexpr()
        with open(self.file, "w") as f:
            f.write(to_write)
     
     
    def set_command(self,instance, bash_file,solver):
        couriers, num_items, item_size, courier_size, distances = instance.unpack()
        courier_dist_ub = instance.courier_dist_ub
        rho_low_bound = instance.rho_low_bound
        courier_dist_lb = instance.courier_dist_lb
        # execution of the bash file
        path = os.path.join(os.getcwd(), bash_file) # path to execute the bash file
        
        command = f"timeout {self.timeout} bash {path} '{self.file}' 'max' '{courier_dist_ub}' '{rho_low_bound-1}' '{solver}' '{couriers}' '{num_items + 1}'"
        return command
    
                         

    
    def solve(self):

        sol_path = self.output_dir + "/SMTlib/"
        strategy = "linear"
        for num, instance in self.data.items():
            json_dict = {}
            couriers, num_items, item_size, courier_size, distances = instance.unpack()

            filename = str(num) + ".json"
            for solver, solverstr in SOLVERS_SMTlib.items():
                print("File = ", num)
                print("Solver used = ", solverstr)
                print("Type search = ", strategy)
                for sym, symstr in SYM_DICT.items():
                    bash_file = "SMT/src/" + strategy + ".sh"
                    self.file = self.instances_dir + str(num).removesuffix('.dat') + ".smt2"
                    
                    self.create_file(instance)
                    
                    command = self.set_command(instance, bash_file, solverstr)
                    
                    print(command) # usciranno 20 camndi uno per istanza
                        
                    print("Starting Execution")
                    start_time = t.time()
                    try:
                        result = subprocess.run(command, shell= True, capture_output= True, text= True)
                        time = t.time() - start_time
                        
                        text = result.stdout
                        val, path = output_formatting(text, num_items + 1)
        

                        out_dict = {
                                'time': time,
                                'optimal': True,
                                'obj':  val,
                                'sol': path
                            }
                    except Exception as e:
                        print("The bash file cannot be executed:", e)
                        out_dict = {
                             'time': self.timeout,
                             'optimal': False,
                             'obj': "n/a",
                             'sol': []
                         }
                        
                    key_dict = solverstr + symstr
                    json_dict[key_dict] = out_dict
                    print(out_dict)
                    save_file(sol_path, filename, out_dict)
                    
        





