# zeroing non instr/data in meminit for bram mem

input_file = "/home/asicfab/a/rrbathin/socet/amp/tensor-core/src/meminit.mem"
memory_size = 65536 

with open(input_file, "r") as f:
    lines = [line.strip() for line in f.readlines()]

while len(lines) < memory_size:
    lines.append("00000000")

lines = lines[:memory_size]

with open(input_file, "w") as f:
    for line in lines:
        f.write(line + "\n")
