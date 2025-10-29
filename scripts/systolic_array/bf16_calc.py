import numpy as np
import struct

def bfloat16_conv(value):
    value = f'{value[2]}{value[3]}{value[0]}{value[1]}' # Hard coded big endian to little endian swap
    #print(value)
    byte_data = bytes.fromhex(value)
    return np.frombuffer(byte_data, dtype=np.bfloat16)[0]

while True:
    instruction = input("command (format: [add/mul/mac] [operand1] [operand2] ([operand3]) )   ").split()
    operands_string = instruction[1::]
    operands_fp = list(map(bfloat16_conv, operands_string))

    print("operands: ", end='')
    for i in range(0, len(operands_string)):
        print(f'{operands_string[i]} aka {operands_fp[i]}, ', end="")
    print("\n")
    
    if(instruction[0] == "mul"):
        result = operands_fp[0] * operands_fp[1]
        result_fp_hex = str(struct.pack(">e", result).hex())
        print(f'result: {result} aka {result_fp_hex}')
    elif(instruction[0] == "add"):
        result = operands_fp[0] + operands_fp[1]
        result_fp_hex = str(struct.pack(">e", result).hex())
        print(f'result: {result} aka {result_fp_hex}')
    elif(instruction[0] == "mac"):
        result = (operands_fp[0] * operands_fp[1]) + operands_fp[2]
        result_fp_hex = str(struct.pack(">e", result).hex())
        print(f'result: {result} aka {result_fp_hex}')
