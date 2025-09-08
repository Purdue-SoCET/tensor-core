import numpy as np

def matrix_to_bytes(nums : np.ndarray):
    assert nums.shape == (4, 4), "Must be 4x4 matrix"
    assert nums.dtype == np.float16, "Must use fp16"
    nums.flatten()
    out = None
    for n in nums:
        if out is None: out = n.tobytes()
        else:           out += n.tobytes()
    return out

def bytes_to_matrix(content : bytes):
        nums = np.array((), dtype = np.float16)
        for c in range(len(content) // 2):
            fl = np.frombuffer(content[2*c:2*c+2], dtype=np.float16)[0]
            nums = np.append(nums, fl)
        nums = nums.reshape((4, 4))
        return nums

if __name__ == "__main__":
    nums = np.array([[3.1415926, -0.5, 55.555, 12.345], 
                         [2.3, 4.555, -6.734, -0.94], 
                         [-00.0089, -3.0002, 21.11, 4.44], 
                         [-0.21718, -3.21, 1.212, 9]],
                        dtype = np.float16)
    m_bytes = matrix_to_bytes(nums)
    nums_in = bytes_to_matrix(m_bytes)
    assert np.allclose(nums, nums_in), "Written and read matrices do not match"

    # Add matrix to data
    out = m_bytes

    # Write to file
    filename = 'test_bin'
    with open(filename, 'wb') as f:
        f.write(out)