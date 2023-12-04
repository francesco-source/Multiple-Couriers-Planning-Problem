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
        
        self.instances_dir = "SMT/src/instances_smtlib/"
        self.output_dir = output_dir
        self.timeout = timeout
        self.file = None
        self.symmetry = None
       
        os.makedirs(self.instances_dir, exist_ok=True) # creating the dir of smtlib file if exists
        self.set_solver()
     
        
       
    def make_smtlib(self, instance, strategy = LINEAR_SEARCH):
        '''
         Initializes the smtlib's file adding logic, constraints, and s-expression
        '''
        self.set_solver() 
        self.set_constraints(instance= instance, strategy= strategy)
        with open(self.file, "w") as file:
            file.write("(set-logic ALL)\n" + self.solver.sexpr())
     
     
    def get_cli(self,instance, bash,solver):
        '''
        Returns the command line instructions to be run
        '''
       
        couriers, num_items, item_size, courier_size, distances = instance.unpack()
        courier_dist_ub = instance.courier_dist_ub
        rho_low_bound = instance.rho_low_bound       
        return f"timeout {self.timeout} bash {os.path.join(os.getcwd(), bash) } '{self.file}' 'max' '{courier_dist_ub}' '{rho_low_bound-1}' '{solver}' '{couriers}' '{num_items + 1}'"
    
                         

    
    def solve(self):
        """
            Runs the solver and saves the results:
                - for each data instance
                - for each solving strategy option
                - for each symmetry breaking option
        """
        strategy = BINARY_SEARCH
        strategy_str = "binary"
        sol_path = self.output_dir + "/SMTlib/" 

        for num, instance in self.data.items():
            couriers, num_items, item_size, courier_size, distances = instance.unpack()
            json_dict = {}
            filename = str(num) + ".json"
           
            for solver, solverstr in SOLVERS_SMTlib.items():
                print("Solver - ", solverstr, " ", strategy_str, " search")
                print("Instance - ", num)
                
                for sym, symstr in SYM_DICT.items():

                    bash = "SMT/src/" + strategy_str + ".sh"
                    self.file = self.instances_dir + str(num).removesuffix('.dat') + ".smt2" 
                    self.make_smtlib(instance)
                    cli = self.get_cli(instance, bash, solverstr)
                    print(cli)
                    print("Starting Execution")
                    start_time = t.time()
                    
                    try:
                        result = subprocess.run(cli, shell= True, capture_output= True, text= True)
                        time = int(t.time() - start_time)
                        text = result.stdout
                        print(result)
                        val, path = output_formatting(text, num_items + 1)
                        if(val == ''):
                            out_dict = {
                            "time": self.timeout,
                            "optimal": False,
                            "obj": "n/a",
                            "sol": []
                            }
                        else:
                              out_dict = {
                                "time": time,
                                "optimal": True,
                                "obj":  int(val),
                                "sol": path
                            }
                        
                      
                    except Exception as e:
                        print("The bash file cannot be executed:", e)
                        out_dict = {
                             'time': self.timeout,
                             'optimal': False,
                             'obj': "n/a",
                             'sol': []
                         }
                        
                    key_dict = strategy_str + "_" + symstr
                    json_dict[key_dict] = out_dict
                    print(out_dict)
                    save_file(sol_path, filename, json_dict)
                    
        





