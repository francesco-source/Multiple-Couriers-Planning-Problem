import argparse

# from cp.src.solver import CPsolver
from SAT.src.solver import SATsolver
from SMT.src.solver import SMTsolver
from MIP.mip import MIPsolver
# from smt.src.smtlib_solver import SMTLIBsolver
# from lp.src.solver import MIPsolver
from utils import load_data


def main():
    parser = argparse.ArgumentParser()

    parser.add_argument("-a", "--approach", help="Select a modelling appraoch between cp sat, smt lp and smtlib",
                        default="cp", type= str)

    parser.add_argument("-m", "--mode", help="Select a mode for the visualization of the solver choosen, either 's' for silent or 'v' for verbose ",
                        default='v', type= str)

    parser.add_argument("-n", "--num_instance",
                        help="Select the instance that you want to solve, default = 0 solve all",
                        default=0, type= int)

    parser.add_argument("-i", "--input_dir",
                        help="Directory where the instance txt files can be found",
                        default="./input", type= str)

    parser.add_argument("-o", "--output_dir",
                        help="Directory where the output will be saved", 
                        default="./res", type= str)

    parser.add_argument("-t", "--timeout", help="Timeout in seconds", default=270, type= int)


    args = parser.parse_args()
    print(args)
    
    if args.num_instance < 0 or args.num_instance > 21: 
        raise argparse.ArgumentError(None, "The number of instance must be an integer in the range [0, 21]")
    if args.timeout <= 0:
        raise TimeoutError("Timeout in seconds must be a positive integer")
    if args.mode not in ('v', 's'):
        raise argparse.ArgumentError(None, "Select a visualization mode between 'v' and 's'")

    print("Loading instances...", end= "")
    data = load_data(args.input_dir, args.num_instance)
    print("Loaded!")  
      
    # if args.approach == "cp":
    #     solver = CPsolver(
    #         data=instance, 
    #         output_dir=args.output_dir, 
        #     timeout=int(args.timeout), 
        #     model=args.model
        # )
    
    if args.approach == "sat":
        solver = SATsolver(
            data=data, 
            output_dir=args.output_dir,
            timeout=int(args.timeout),
            mode=args.mode
        )

    elif args.approach == "smt":
        solver = SMTsolver(
            data=data,
            output_dir=args.output_dir,
            timeout=int(args.timeout),
            mode=args.mode
        )
    
    # elif args.approach == "smtlib":
    #     solver = SMTLIBsolver(
    #         data=data,
    #         output_dir=args.output_dir,
    #         timeout=int(args.timeout)
    #         )

    elif args.approach == "lp":
        solver = MIPsolver(
            data=data,
            output_dir=args.output_dir,
            timeout=int(args.timeout),
            mode=args.mode)
        
    else:
        raise argparse.ArgumentError(None, "Please select a solver between cp, sat, smt lp and smtlib")

    print("Solving with", args.approach)
    solver.solve()


if __name__ == '__main__':
    main()
