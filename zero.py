
input_file = "/home/asicfab/a/rrbathin/socet/amp/tensor-core/src/meminit.mem"
memory_size = 65536  # 64K addresses

# Read existing lines
with open(input_file, "r") as f:
    lines = [line.strip() for line in f.readlines()]

# Pad with 00000000 if file is too short
while len(lines) < memory_size:
    lines.append("00000000")

# Truncate if file is too long (optional safety step)
lines = lines[:memory_size]

# Overwrite original file
with open(input_file, "w") as f:
    for line in lines:
        f.write(line + "\n")
