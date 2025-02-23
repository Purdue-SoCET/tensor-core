import numpy as np
import sys
filename = sys.argv[1]
# Read matrices from input.txt
with open(f"{filename}.txt", "r") as f:
    lines = f.readlines()

# Convert text file contents into matrices
weight_matrix = []
input_matrix = []
partial_sum_matrix = []
result = []
flag = "None"  # To track which matrix is being read

for line in lines:
    if line.strip() == "Weights":
        flag = "Weights"
        weight_matrix = []
        continue
    elif line.strip() == "Inputs":
        flag = "Inputs"
        input_matrix = []
        continue
    elif line.strip() == "Partials":
        flag = "Partials"
        partial_sum_matrix = []
        continue
    elif line.strip() == "Multiply":
        # Convert to NumPy arrays
        W = np.array(weight_matrix)
        I = np.array(input_matrix)
        PS = np.array(partial_sum_matrix)
        # Perform matrix multiplication
        result_matrix = np.dot(W, I) + PS
        for i in range(4):
            result.append(result_matrix[i])
        continue
    
    row = list(map(int, line.strip().split()))
    if (flag == "Weights"):
        weight_matrix.append(row)
    elif (flag == "Inputs"):
        input_matrix.append(row)
    elif (flag == "Partials"):
        partial_sum_matrix.append(row)
# Write result to output.txt
with open(f"{filename}_output.txt", "w") as f:
    for row in result:
        f.write(" ".join(map(str, row)) + "\n")