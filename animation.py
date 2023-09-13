import argparse
from utils import *
from check_solution import read_json_file
import numpy as np
import seaborn as sns
import matplotlib.pyplot as plt
from sklearn.manifold import MDS

def main():
    parser = argparse.ArgumentParser()

    parser.add_argument("-a", "--approach", help="Select a modelling appraoch between cp sat, smt lp and smtlib",
                        default="cp", type= str)

    parser.add_argument("-n", "--num_instance",
                        help="Select the instance for which you want to visualize the result, default = 1",
                        default=1, type= int)

    parser.add_argument("-i", "--input_dir",
                        help="Directory where the instance txt files can be found",
                        default="./input", type= str)

    parser.add_argument("-o", "--output_dir",
                        help="Directory where the output will be saved", 
                        default="./res", type= str)

    args = parser.parse_args()
    print(args)

    instance = load_instance(args.input_dir, args.num_instance, preprocessing= False)
    m, n, _, _, D = instance.unpack()

    if args.approach == "cp":
        apprstr = "/CP/"
    
    elif args.approach == "sat":
        apprstr = "/SAT/"
    
    elif args.approach == "smt":
        apprstr = "/SMT/"
    
    elif args.approach == "smtlib":
        apprstr = "/SMTLIB/"

    elif args.approach == "lp":
        apprstr = "/MIP/"
    
    output_path = args.output_dir + apprstr + str(args.num_instance) + ".json"
    inst_result = read_json_file(output_path)

    # Firstly, make the distance matrix symmetric. Average out the nonsymmetric parts
    dist_matrix = D
    sym_matrix = (dist_matrix + dist_matrix.T) / 2

    # Create color palette associated to the courier
    palette = sns.color_palette("husl", n_colors= m)

    n_solvers = len(inst_result)
    plt.figure(figsize= (5 * 2, 4 * (1 + n_solvers) // 2))
    i_solver = 1
    plt.suptitle(f"Instance {args.num_instance} graphic solution with {args.approach}")

    for solver, solver_result in inst_result.items():
        solution = solver_result["sol"]

        mds = MDS(n_components=2, dissimilarity='precomputed', normalized_stress= "auto", random_state=42)
        coordinates = mds.fit_transform(sym_matrix)

        # The last point is the deposit. This is meant to be the origin of the frame of reference
        coordinates = coordinates - coordinates[-1]

        plt.subplot((1 + n_solvers) // 2, 2, i_solver)
        plt.scatter(coordinates[:-1, 0], coordinates[:-1, 1], c='b', s=40, marker='h')
        plt.scatter(coordinates[-1, 0], coordinates[-1, 1], c='black', s=100, marker='s')

        for i_courier, courier_path in enumerate(solution):
            plt.arrow(0, 0, coordinates[courier_path[0]-1, 0], coordinates[courier_path[0]-1, 1], 
                      color= palette[i_courier], head_width = 0.1, length_includes_head= True)
            
            for i_item in range(len(courier_path)-1):
                plt.arrow(x= coordinates[courier_path[i_item]-1, 0], 
                          y= coordinates[courier_path[i_item]-1, 1], 
                          dx= coordinates[courier_path[i_item+1]-1, 0] - coordinates[courier_path[i_item]-1, 0], 
                          dy= coordinates[courier_path[i_item+1]-1, 1] - coordinates[courier_path[i_item]-1, 1], 
                          color= palette[i_courier], head_width = 0.1, length_includes_head= True)
                
            plt.arrow(x= coordinates[courier_path[-1]-1, 0], 
                      y= coordinates[courier_path[-1]-1, 1],
                      dx= -coordinates[courier_path[-1]-1, 0], 
                      dy= -coordinates[courier_path[-1]-1, 1], 
                      color= palette[i_courier], head_width = 0.1, length_includes_head= True)
                
        for i, coord in enumerate(coordinates[:-1]):
            plt.annotate(f'{i+1}', (coord[0], coord[1]))
        
        plt.xlabel("X")
        plt.ylabel("Y")
        plt.grid(True)
        plt.title(f"Solver: {solver}")
        i_solver += 1
    
    
    plt.show()



if __name__ == "__main__":
    main()