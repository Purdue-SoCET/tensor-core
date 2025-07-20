import uvm_pkg::*;
`include "uvm_macros.svh"
`include "transaction.svh"

class predictor extends uvm_subscriber#(transaction);
  `uvm_component_utils(predictor)

  uvm_analysis_port#(transaction) pred_ap;
  transaction output_tx;

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction: new

  function void build_phase(uvm_phase phase);
    pred_ap = new("pred_ap", this);
  endfunction

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


  function void write(transaction t);
    output_tx = transaction#(4)::type_id::create("output_tx", this); 
    output_tx.copy(t);

    // calculate expected sum and expected overflow

    // for(int i =0;i < 4;i++) begin
    //   output_tx.out_matrix[i][j] = t.partial_matrix[i][j];
    //     for(int j = 0; j < 4; j++) begin

    //       for(int k = 0; k < 4; k++) begin
    //       output_tx.out_matrix[i][((j+1)*16)-1 : j*16] += t.input_matrix[i][j+k] * t.weight_matrix[i+k][((j+1)*16)-1 : j*16];
    //       end
    //     end
    // end
    // {output_tx.out_matrix} = (t.input_matrix * t.weight_matrix + t.partial_matrix);


  for (int i = 0; i < 4; i++) begin
    for (int j = 0; j < 4; j++) begin
      real sum = half_to_real(t.partial_matrix[i][j*DW +: DW]);
      for (int k = 0; k < 4; k++) begin
        sum += half_to_real(t.input_matrix[i][k*DW +: DW]) * half_to_real(t.weight_matrix[k][j*DW +: DW]);
      end
      output_tx.out_matrix[i][j*DW +: DW] = real_to_half(sum);
    end
  end
    
    // send expected output to scoreboard
    pred_ap.write(output_tx);
  endfunction: write
endclass: predictor
