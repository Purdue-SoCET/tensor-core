#!/usr/bin/env python3
"""
BF16 Multiplication Test Script
Tests bf16 multiplication results from mul_bf16.sv against PyTorch reference implementation.
"""

import torch
import struct

def hex_to_bf16(hex_val):
    """Convert 16-bit hex value to bfloat16 tensor."""
    # BF16 format: 1 sign bit, 8 exponent bits, 7 mantissa bits
    # We need to convert to FP32 first, then to BF16
    # BF16 is essentially the upper 16 bits of FP32
    
    # Extend BF16 to FP32 by adding 16 zero bits at the end
    fp32_bits = (hex_val << 16)
    
    # Convert bits to float
    fp32_val = struct.unpack('!f', struct.pack('!I', fp32_bits))[0]
    
    return torch.tensor(fp32_val, dtype=torch.float32).to(torch.bfloat16)

def bf16_to_hex(bf16_tensor):
    """Convert bfloat16 tensor to 16-bit hex value."""
    # Convert to FP32 first
    fp32_val = bf16_tensor.to(torch.float32).item()
    
    # Get the bits
    fp32_bits = struct.unpack('!I', struct.pack('!f', fp32_val))[0]
    
    # Extract upper 16 bits (BF16)
    bf16_bits = (fp32_bits >> 16) & 0xFFFF
    
    return bf16_bits

def test_mul_bf16():
    """Test the multiplication results from the testbench."""
    
    # Test sets from mul_bf16_tb.sv
    test_set1 = [
        0x4720, 0x4491, 0x487e, 0x456f, 0x4854,
        0x458b, 0x403f, 0x489e, 0x47e0, 0x48f0
    ]
    
    test_set2 = [
        0x41c1, 0x4620, 0x4849, 0x46fd, 0x463c,
        0x4420, 0x3ff3, 0x435c, 0x40b1, 0x43fa
    ]
    
    print("BF16 Multiplication Test Results")
    print("=" * 80)
    print(f"{'Index':<6} {'A (hex)':<10} {'B (hex)':<10} {'A (dec)':<12} {'B (dec)':<12} {'Result (hex)':<12} {'Result (dec)':<12}")
    print("=" * 80)
    
    results_hex = []
    results_dec = []
    
    for i in range(len(test_set1)):
        # Convert hex to bf16
        a_bf16 = hex_to_bf16(test_set1[i])
        b_bf16 = hex_to_bf16(test_set2[i])
        
        # Perform multiplication in bf16
        result_bf16 = a_bf16 * b_bf16
        
        # Convert result back to hex
        result_hex = bf16_to_hex(result_bf16)
        
        # Store results
        results_hex.append(result_hex)
        results_dec.append(result_bf16.item())
        
        # Print results
        print(f"{i:<6} 0x{test_set1[i]:04x}     0x{test_set2[i]:04x}     "
              f"{a_bf16.item():<12.6f} {b_bf16.item():<12.6f} "
              f"0x{result_hex:04x}       {result_bf16.item():<12.6f}")
    
    print("=" * 80)
    print("\nExpected results for SystemVerilog verification:")
    print("Copy these hex values to compare with your waveform:")
    print("-" * 80)
    for i, hex_val in enumerate(results_hex):
        print(f"Test {i}: 0x{hex_val:04x}")
    
    print("\n" + "=" * 80)
    print("Instructions for GTKWave verification:")
    print("1. Run the testbench: verilator --binary -j 0 -Wall -Wno-fatal mul_bf16_tb")
    print("   -Imodules -Itestbench -Iinclude --hierarchical --trace")
    print("2. Execute: ./obj_dir/Vmul_bf16_tb")
    print("3. Open GTKWave: gtkwave waves/mul_bf16_waves.vcd")
    print("4. Compare tb_result signal with the hex values above")
    print("=" * 80)

if __name__ == "__main__":
    test_mul_bf16()
