
# mac_expectations.py
# Compute expected FP16 MAC outputs for the SystemVerilog tb vectors.
# out_accumulate = in_accumulate + in_value * weight
#
# Usage: python mac_expectations.py
#
# Prints a table:
#   Input(hex) Weight(hex) InAcc(hex)  ->  Out(hex)   (and their float interpretations)

import struct
import numpy as np

# --- Helpers --------------------------------------------------------------
def f16_from_hex_be(h4: str) -> float:
    """Convert 4-hex-digit big-endian (e.g., '4720') to Python float via IEEE-754 half."""
    h4 = h4.strip().lower()
    if h4.startswith('16\'h') or h4.startswith('16\'H'):
        h4 = h4.split('h')[-1]
    if len(h4) != 4:
        raise ValueError(f"Expected 4 hex digits, got: {h4}")
    return struct.unpack('>e', bytes.fromhex(h4))[0]

def hex_be_from_f16(val: float) -> str:
    """Convert Python float to big-endian 4-hex-digit IEEE-754 half string (uppercase)."""
    # Force to float16 before pack, then pack as big-endian half ('>e')
    b = struct.pack('>e', np.float16(val).item())
    return b.hex().upper()

# --- Testbench Vectors (big-endian hex, matching 16'hXXXX) ----------------
test_inputs  = ["4720","4491","487e","456f","4854","458b","403f","489e","47e0","48f0"]
test_weights = ["41c1","4620","4849","46fd","463c","4420","3ff3","435c","40b1","43fa"]
test_ps      = ["48c9","3cf0","40dd","48ac","47fd","3e2c","476f","47a8","3dba","4388"]

# --- Compute --------------------------------------------------------------
rows = []
for i in range(len(test_inputs)):
    in_hex  = test_inputs[i]
    wt_hex  = test_weights[i]
    ps_hex  = test_ps[i]

    in_f  = f16_from_hex_be(in_hex)
    wt_f  = f16_from_hex_be(wt_hex)
    ps_f  = f16_from_hex_be(ps_hex)

    # Emulate FP16 pipeline behavior: round after each op using numpy.float16
    prod_f16 = np.float16(in_f) * np.float16(wt_f)
    out_f16  = np.float16(ps_f) + np.float16(prod_f16)

    out_hex = hex_be_from_f16(out_f16)

    rows.append((i, in_hex.upper(), wt_hex.upper(), ps_hex.upper(), out_hex, float(in_f), float(wt_f), float(ps_f), float(prod_f16), float(out_f16)))

# --- Print ---------------------------------------------------------------
header = (
    f"{'idx':>3}  {'Input':>6}  {'Weight':>6}  {'InAcc':>6}   ->   {'Out':>6}"
    f"    |   in_f        wt_f        ps_f        prod_f16     out_f16"
)
print(header)
print('-' * len(header))
for i, in_hex, wt_hex, ps_hex, out_hex, in_f, wt_f, ps_f, prod_f16, out_f16 in rows:
    print(f"{i:3d}  {in_hex:>6}  {wt_hex:>6}  {ps_hex:>6}   ->   {out_hex:>6}"
          f"    |   {in_f:>10.6f}  {wt_f:>10.6f}  {ps_f:>10.6f}  {prod_f16:>12.6f}  {out_f16:>10.6f}")

# Also print a simple line-per-vector format similar to the SV $display()
print("\nSV-style lines:")
for i, in_hex, wt_hex, ps_hex, out_hex, *_ in rows:
    print(f"Input: {in_hex}   Weight: {wt_hex}   in_acc: {ps_hex}    Expected Output: {out_hex}")
