import numpy as np
import struct
import sys
sysarr_values_file = sys.argv[1]
python_values_file = sys.argv[2]
print(sysarr_values_file)
print(python_values_file)
output_log_file = open(sys.argv[3], "w")

mat_size = 4

# Read matrices from input.txt
with open(sysarr_values_file, "r") as f:
    sysarr_lines = f.readlines()

with open(python_values_file, "r") as f:
    python_lines = f.readlines()

incorrect_count = 0
total_count = 0


def float16_conv(value):
    value = f'{value[2]}{value[3]}{value[0]}{value[1]}' # Hard coded big endian to little endian swap
    #print(value)
    byte_data = bytes.fromhex(value)
    return np.frombuffer(byte_data, dtype=np.float16)[0]

for i in range(0, len(sysarr_lines)):
    sysarr_line_hex = sysarr_lines[i].strip().split()
    python_line_hex = python_lines[i].strip().split()

    sysarr_line_values = list(map(float16_conv, sysarr_line_hex))
    python_line_values = list(map(float16_conv, python_line_hex))
    
    matrix_num = i // mat_size
    row_num = i % mat_size

    print(row_num)
    print(sysarr_line_hex)
    print(sysarr_line_values)
    print(python_line_hex)
    print(python_line_values)


    for j in range(0, len(sysarr_line_values)):
        total_count = total_count + 1
        if sysarr_line_values[j] != python_line_values[j]:
            incorrect_count = incorrect_count + 1
            difference = abs(sysarr_line_values[j] - python_line_values[j]) / python_line_values[j] * 100
            output_log_file.write(f'matrix {matrix_num} row {row_num} col {j}: sysarr output {sysarr_line_hex[j]} ({sysarr_line_values[j]}), python output {python_line_hex[j]} ({python_line_values[j]}). error: {difference}%\n')

output_log_file.write(f'total values: {total_count} mismatching values: {incorrect_count}')
output_log_file.close()