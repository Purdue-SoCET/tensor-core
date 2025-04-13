input_file = "mergesort.hex"
output_file = "mergesort_word.hex"

with open(input_file, 'r') as f:
    tokens = f.read().split()

tokens = [t for t in tokens if not t.startswith('@')]

with open(output_file, 'w') as f:
    for i in range(0, len(tokens), 4):
        if i + 3 >= len(tokens):
            break
        # Little-endian format: byte3 byte2 byte1 byte0
        b0 = tokens[i]
        b1 = tokens[i + 1]
        b2 = tokens[i + 2]
        b3 = tokens[i + 3]
        word = b3 + b2 + b1 + b0
        f.write(f"{word.upper()}\n")
