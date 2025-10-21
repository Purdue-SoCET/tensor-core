import numpy as np
import csv

N = 2000  # number of random cases
np.random.seed(67)

# Random 16-bit value from 0x0000 → 0xFFFF
def random_fp16_bits():
    return np.random.randint(0, 0x10000)

# Turn into float16
def fp16_from_bits(bits):
    return np.frombuffer(np.uint16(bits).tobytes(), dtype=np.float16)[0]

with open("random_cases.csv", "w", newline="") as f:
    writer = csv.writer(f)
    writer.writerow(["a", "b", "sub", "expected"])

    for _ in range(N):
        a_bits = random_fp16_bits()
        b_bits = random_fp16_bits()
        sub = np.random.randint(0, 2)

        # Compute expected result, may change this to pytorch eventually
        a_val = fp16_from_bits(a_bits)
        b_val = fp16_from_bits(b_bits)
        exp_val = np.float16(a_val - b_val if sub else a_val + b_val)

        exp_bits = np.frombuffer(exp_val.tobytes(), dtype=np.uint16)[0]
        writer.writerow([f"{a_bits:04x}", f"{b_bits:04x}", sub, f"{exp_bits:04x}"])