import random
import sys
import struct

def float_to_fp16_bits(value):
    """Convert Python float to IEEE 754 half-precision bits (as int)."""
    f32 = struct.pack('>f', value)
    f32_bits = struct.unpack('>I', f32)[0]

    sign = (f32_bits >> 31) & 0x1
    exp = (f32_bits >> 23) & 0xFF
    frac = f32_bits & 0x7FFFFF

    # FP32 bias = 127, FP16 bias = 15
    if exp == 0xFF:  # Inf or NaN
        fp16_exp = 0x1F
        fp16_frac = 0 if frac == 0 else 0x200  # NaN handled later
    elif exp > 142:  # Overflow -> Inf
        fp16_exp = 0x1F
        fp16_frac = 0
    elif exp < 113:  # Underflow -> Zero (no subnormals)
        fp16_exp = 0
        fp16_frac = 0
    else:
        fp16_exp = exp - 112
        fp16_frac = frac >> 13

    return (sign << 15) | (fp16_exp << 10) | fp16_frac

def is_subnormal_fp16(value):
    exponent = (value >> 10) & 0x1F
    mantissa = value & 0x3FF
    return exponent == 0 and mantissa != 0

def generate_fp16_value():
    """Generate a random FP16 bit pattern (no subnormals, NaNs allowed)."""
    while True:
        # Random sign
        sign = random.randint(0, 1)
        # Random exponent: 0–31 (allow all including 31 for Inf/NaN)
        exp = random.randint(0, 0x1F)
        # Random mantissa (10 bits)
        mantissa = random.randint(0, 0x3FF)

        bits = (sign << 15) | (exp << 10) | mantissa
        if not is_subnormal_fp16(bits):
            return bits

def generate_test_case():
    """Generate a single random test case."""
    vector = [f"{generate_fp16_value():04x}" for _ in range(32)]
    op = random.randint(0, 2)

    # Generate broadcast/clear bits (never both 1)
    if random.random() < 0.5:
        broadcast = random.randint(0, 1)
        clear = 0 if broadcast == 1 else random.randint(0, 1)
    else:
        clear = random.randint(0, 1)
        broadcast = 0 if clear == 1 else random.randint(0, 1)

    index = random.randint(0, 31)
    vector_str = ','.join(vector)
    return f"{vector_str},{op},{broadcast},{clear},{index}"

def main():
    num_cases = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    for _ in range(num_cases):
        print(generate_test_case())

if __name__ == "__main__":
    main()