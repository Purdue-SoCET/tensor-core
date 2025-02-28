import math

def clog2(x):
    """Return the ceiling of log2(x)."""
    return math.ceil(math.log2(x))

# Given parameters
CACHE_SIZE = 1024       # e.g., bytes
BLOCK_SIZE = 4
NUM_WAYS = 4
NUM_BANKS = 4
MSHR_BUFFER_LEN = 8
CACHE_RW_SIZE = 32

# Derived local parameters
# Assuming CACHE_SIZE/4 converts cache size to words (if each word is 4 bytes)
NUM_SETS = (CACHE_SIZE // 4) // (BLOCK_SIZE * NUM_WAYS)
NUM_SETS_PER_BANK = NUM_SETS // NUM_BANKS
BYTE_OFF_BIT_LEN = 2
BLOCK_OFF_BIT_LEN = clog2(BLOCK_SIZE)  # selects which block within a bank
BLOCK_INDEX_BIT_LEN = clog2(NUM_SETS)   # selects the set index
WAYS_LEN = clog2(NUM_WAYS)
BANKS_LEN = clog2(NUM_BANKS)
TAG_BIT_LEN = 32 - BLOCK_INDEX_BIT_LEN - BLOCK_OFF_BIT_LEN - BYTE_OFF_BIT_LEN

# Print the results
print("Calculated Cache Parameters:")
print("-------------------------------")
print(f"CACHE_SIZE         = {CACHE_SIZE}")
print(f"BLOCK_SIZE         = {BLOCK_SIZE}")
print(f"NUM_WAYS           = {NUM_WAYS}")
print(f"NUM_BANKS          = {NUM_BANKS}")
print(f"MSHR_BUFFER_LEN    = {MSHR_BUFFER_LEN}")
print(f"CACHE_RW_SIZE      = {CACHE_RW_SIZE}")
print("")
print(f"NUM_SETS           = {NUM_SETS}")
print(f"NUM_SETS_PER_BANK  = {NUM_SETS_PER_BANK}")
print(f"BYTE_OFF_BIT_LEN   = {BYTE_OFF_BIT_LEN}")
print(f"BLOCK_OFF_BIT_LEN  = {BLOCK_OFF_BIT_LEN}")
print(f"BLOCK_INDEX_BIT_LEN= {BLOCK_INDEX_BIT_LEN}")
print(f"WAYS_LEN           = {WAYS_LEN}")
print(f"BANKS_LEN          = {BANKS_LEN}")
print(f"TAG_BIT_LEN        = {TAG_BIT_LEN}")
