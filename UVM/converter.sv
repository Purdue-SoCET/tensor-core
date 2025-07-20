/**
 * @ Author: Adithya Narayanan
 * @ Create Time: 2025-07-19 21:15:07
 * @ Modified by: Adithya Narayanan
 * @ Modified time: 2025-07-19 21:44:32
 * @ Description:
 */
module float_to_real;

// Function to convert half-precision floating point to real
  function real half_to_real(input logic [15:0] half);
    logic sign;
    logic [4:0] exponent;
    logic [9:0] fraction;
    integer exp_val;
    real result, mantissa;

    begin
      sign     = half[15];
      exponent = half[14:10];
      fraction = half[9:0];

      // Special cases
      if (exponent == 5'b00000) begin
        if (fraction == 10'b0)
          result = 0.0; // Zero
        else begin
          // Subnormal number: exponent = -14, no implicit 1
          mantissa = fraction / 1024.0; // 2^10 = 1024
          result = mantissa * (2.0 ** -14);
        end
      end else if (exponent == 5'b11111) begin
        if (fraction == 10'b0)
          result = 1.0 / 0.0; // Infinity
        else
          result = 0.0 / 0.0; // NaN
      end else begin
        // Normalized number
        mantissa = 1.0 + (fraction / 1024.0); // Add implicit leading 1
        exp_val = exponent - 15;
        result = mantissa * (2.0 ** exp_val);
      end

      // Apply sign
      if (sign)
        result = -result;

      return result;
    end
  endfunction

function automatic logic [15:0] real_to_half(input real val);
  logic        sign;
  int          exponent, biased_exp, mantissa;
  real         abs_val, normalized;
  logic [15:0] result;

  begin
    // Handle special cases
    if (val == 0.0) begin
      return 16'h0000; // +0
    end else if (val == 1.0 / 0.0) begin
      return 16'h7C00; // +Inf
    end else if (val == -1.0 / 0.0) begin
      return 16'hFC00; // -Inf
    end else if (val != val) begin
      return 16'h7E00; // NaN
    end

    // Sign and absolute value
    sign = (val < 0.0);
    abs_val = (sign) ? -val : val;

    // Compute base-2 exponent
    exponent = $rtoi($floor($ln(abs_val) / $ln(2.0)));
    biased_exp = exponent + 15;

    // Normalize abs_val to [1.0, 2.0) range
    normalized = abs_val / (2.0 ** exponent);

    // Extract mantissa (remove implicit 1)
    mantissa = $rtoi((normalized - 1.0) * 1024.0); // 10-bit mantissa

    // Handle overflow
    if (biased_exp >= 31) begin
      return {sign, 5'b11111, 10'b0}; // Inf
    end

    // Handle subnormal
    if (biased_exp <= 0) begin
      if (biased_exp < -10) begin
        return 16'h0000; // Too small => 0
      end
      mantissa = $rtoi(abs_val * (2.0 ** (10 + 14))); // scale to subnormal
      return {sign, 5'b00000, mantissa[9:0]};
    end

    // Normal case
    result = {sign, biased_exp[4:0], mantissa[9:0]};
    return result;
  end
endfunction


initial begin
    // Example usage of the half_to_real function
    logic [15:0] half_value [7:0]= {16'h3c00, 16'hd8ab, 16'habcd, 16'hffff, 16'h0000, 16'hefc8, 16'h75ba, 16'hff00}; // Example half-precision value (1.0 in half-precision)
    real real_value;
    logic [15:0] half_value_gen;
    
    foreach(half_value[i]) begin
        real_value = half_to_real(half_value[i]);
        half_value_gen = real_to_half(real_value); // Convert back to half-precision for verification
        $display("Half-precision value: %h, Converted to real: %f, Converted float: %h", half_value[i], real_value, half_value_gen);
    end

    #10 $finish; // End simulation after displaying the result
end

endmodule