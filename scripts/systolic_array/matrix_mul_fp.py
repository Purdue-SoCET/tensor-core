import numpy as np
import sys
import struct
filename = sys.argv[1]

mat_size = 4

# Read matrices from input.txt
with open(f"{filename}.txt", "r") as f:
    lines = f.readlines()

# Convert text file contents into matrices
weight_matrix = []
input_matrix = []
partial_sum_matrix = []
result = []
flag = "None"  # To track which matrix is being read

def float16_conv(value):
    value = f'{value[2]}{value[3]}{value[0]}{value[1]}' # Hard coded big endian to little endian swap
    #print(value)
    byte_data = bytes.fromhex(value)
    return np.frombuffer(byte_data, dtype=np.float16)[0]

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
        W = np.array(weight_matrix, dtype=np.float16)
        print(W)
        I = np.array(input_matrix, dtype=np.float16)
        print(I)
        PS = np.array(partial_sum_matrix, dtype=np.float16)
        print(PS)
        # Perform matrix multiplication0.

        result_matrix = [[0 for _ in range(mat_size)] for _ in range(mat_size)]
        # Perform matrix multiplication
        for i in range(len(result_matrix)):  # Iterate over rows of A
            for j in range(len(result_matrix[i])):  # Iterate over columns of B
                for k in range(mat_size):  # Sum over A row * B column
                    result_matrix[i][j] += W[i][k] * I[k][j]
        result_matrix = result_matrix + PS
        # result_matrix = np.dot(W, I) + PS
        for i in range(mat_size):
            result.append(result_matrix[i])
        continue
    
    row = list(map(float16_conv, line.strip().split()))
    # print(f'Row: {row}')
    if (flag == "Weights"):
        weight_matrix.append(row)
    elif (flag == "Inputs"):
        input_matrix.append(row)
    elif (flag == "Partials"):
        partial_sum_matrix.append(row)
# Write result to output.txt
with open(f"{filename}_output.txt", "w") as f:
    for row in result:
        to_write = [str(struct.pack(">e", item).hex()) for item in row]
        to_write = " ".join(to_write)
        f.write((to_write) + "\n")