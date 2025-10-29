import numpy as np
import struct
import sys
filename = sys.argv[1]
# Read matrices from input.txt
with open(f"{filename}.txt", "r") as f:
    lines = f.readlines()

output = []
for line in lines:
    if not line[0].isnumeric():
        output.append(line)
        continue
    row = list(map(float, line.strip().split()))
    row = np.array(row)
    row = row.astype(np.float16)
    row = [str(struct.pack(">e", item).hex()) for item in row]
    row = " ".join(row)
    row += "\n"
    output.append(row)

with open(f"{filename}_encoded.txt", "w") as outfile:
    for line in output:
        outfile.writelines(line)
