import subprocess
import os 
import time 
from SMT.src.solver import SMTsolver
from SMT.src.SMT_utils import *
from utils import *
from constants import *

class SMTLIBsolver(SMTsolver):
    
    def __init__(self,data,output_dir, timeout = 300, mode = "v"):
        super().__init__(data,output_dir=output_dir,timeout = timeout, mode = mode)
        self.set_optimizer()
        self.instances_dir = "smt/src/instances_smtlib/"
        os.makedirs(self.instances_dir, exist_ok=True) # creating the dir of smtlib file if exists
        self.output_dir = output_dir
        self.timeout = timeout
        self.set_optimizer()
        self.symmetry = None
        self.file = None
        
    def set_optimizer(self):
        """
        The optimizer cannot be written because we do not have a command maximize/minimize
        for smtlib files
        """
        
        self.optimizer = Solver()
        self.optimizer.set(timeout=self.timeout * 1000)
        
    def set_model(self,instance,strategy = "binary"):
        """
        This function is created in the case we want to extend the experiments for the other model
        for now the file smtlib are set for the best model (model zero)
        """
        
        vars = self.set_constraints(instance=instance,strategy = strategy)
        
       
    def create_file(self,instance,strategy = "binary"):
        # smtlib instruction to suppress warning for using different solvers
        self.set_optimizer() # setting the Solver to create the model
        self.set_model(instance) # setting of the model used
        to_write = "(set-logic ALL)\n" 
        to_write += self.optimizer.sexpr()
        with open(self.file, "w") as f:
            f.write(to_write)
     
     
    def set_command(self,instance, bash_file,solver):
        couriers, num_items,item_size, courier_size, distances = instance.unpack()
        courier_dist_ub = instance.courier_dist_ub
        rho_low_bound = instance.rho_low_bound
        courier_dist_lb = instance.courier_dist_lb
        # execution of the bash file
        path = os.path.join(os.getcwd(),bash_file) # path to execute the bash file
        
        command = f"timeout {self.timeout} bash {path} '{self.file}' 'max' '{upper_bound}' '{lower_bound -1}' '{solver}' '{couriers}' '{num_items + 1}'"
        return command
    
    
    
    
        

