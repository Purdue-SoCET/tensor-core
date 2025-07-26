import uvm_pkg::*;
`include "uvm_macros.svh"
`include "transaction.svh"

class predictor extends uvm_subscriber#(transaction);
  `uvm_component_utils(predictor)

  uvm_analysis_port#(transaction) pred_ap;
  transaction output_tx;

  localparam int DW = 16; // FP16 bit-width

  function new(string name, uvm_component parent = null);
    super.new(name, parent);
  endfunction: new

  function void build_phase(uvm_phase phase);
    pred_ap = new("pred_ap", this);
  endfunction


  // Check if real value is same as IEEE 754 representation.
  // Convert FP16 to real
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

      if (exponent == 5'b00000) begin
        if (fraction == 10'b0)
          result = 0.0;
        else begin
          mantissa = fraction / 1024.0;
          result = mantissa * (2.0 ** -14);
        end
      end else if (exponent == 5'b11111) begin
        if (fraction == 10'b0)
          result = 1.0 / 0.0;
        else
          result = 0.0 / 0.0;
      end else begin
        mantissa = 1.0 + (fraction / 1024.0);
        exp_val = exponent - 15;
        result = mantissa * (2.0 ** exp_val);
      end

      if (sign)
        result = -result;

      return result;
    end
  endfunction

  // Convert real to FP16
  function automatic logic [15:0] real_to_half(input real val);
    logic        sign;
    int          exponent, biased_exp, mantissa;
    real         abs_val, normalized;
    logic [15:0] result;

    begin
      if (val == 0.0) return 16'h0000;
      else if (val == 1.0 / 0.0) return 16'h7C00;
      else if (val == -1.0 / 0.0) return 16'hFC00;
      else if (val != val) return 16'h7E00;

      sign = (val < 0.0);
      abs_val = (sign) ? -val : val;

      exponent = $rtoi($floor($ln(abs_val) / $ln(2.0)));
      biased_exp = exponent + 15;
      normalized = abs_val / (2.0 ** exponent);
      mantissa = $rtoi((normalized - 1.0) * 1024.0);

      if (biased_exp >= 31) return {sign, 5'b11111, 10'b0};
      if (biased_exp <= 0) begin
        if (biased_exp < -10) return 16'h0000;
        mantissa = $rtoi(abs_val * (2.0 ** (10 + 14)));
        return {sign, 5'b00000, mantissa[9:0]};
      end

      result = {sign, biased_exp[4:0], mantissa[9:0]};
      return result;
    end
  endfunction


    real input_real[4][4];
    real weight_real[4][4];
    real partial_real[4][4];
    real result_real[4][4];

  function void rotate_anticlockwise(ref real mat[4][4]);
  real temp[4][4];
  
  // Copy original matrix into temp
  for (int i = 3; i >=0; i--) begin
    for (int j = 3; j >=0; j--) begin
      temp[i][j] = mat[i][j];
    end
  end

  // Rotate anticlockwise
  for (int i = 3; i >=0; i--) begin
    for (int j = 3; j >=0; j--) begin
      mat[i][j] = temp[j][4-1-i];
    end
  end
endfunction


  function void write(transaction t);
    output_tx = transaction#(4)::type_id::create("output_tx", this); 
    output_tx.copy(t);


    // Convert all FP16 matrices to real
    for (int i = 3; i >=0; i--) begin
      for (int j = 3; j >=0; j--) begin
        input_real[i][j]   = half_to_real(t.input_matrix[i][j*DW +: DW]);
        weight_real[i][j]  = half_to_real(t.weight_matrix[i][j*DW +: DW]);
        partial_real[i][j] = half_to_real(t.partial_matrix[i][j*DW +: DW]);
      end
    end
    rotate_anticlockwise(input_real);
    rotate_anticlockwise(weight_real);
    rotate_anticlockwise(partial_real);
    // Perform matrix multiplication and addition
    for (int i = 3; i >=0; i--) begin
      for (int j = 3; j >=0; j--) begin
        real sum = partial_real[i][j];
        for (int k = 0; k < 4; k++) begin
          sum += input_real[i][k] * weight_real[k][j];
        end
        result_real[i][j] = sum;
        output_tx.out_matrix[i][j*DW +: DW] = real_to_half(sum);
      end
    end

    
    `uvm_info("PREDICTOR", "Input Matrix (FP16, hex):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%h ", output_tx.input_matrix[i][j*DW +: DW])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

        `uvm_info("PREDICTOR", "Weight Matrix (FP16, hex):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%h ", output_tx.weight_matrix[i][j*DW +: DW])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

    // Print matrices using uvm_info
    `uvm_info("PREDICTOR", "Input Matrix (real):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%0.5f ", input_real[i][j])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

    `uvm_info("PREDICTOR", "Weight Matrix (real):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%0.5f ", weight_real[i][j])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

    `uvm_info("PREDICTOR", "Partial Matrix (real):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%0.5f ", partial_real[i][j])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

    `uvm_info("PREDICTOR", "Output Matrix (real):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%0.5f ", result_real[i][j])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

    `uvm_info("PREDICTOR", "Output Matrix (FP16, hex):", UVM_MEDIUM)
    for (int i = 3; i >=0; i--) begin
      string row = "[ ";
      for (int j = 3; j >=0; j--) row = {row, $sformatf("%h ", output_tx.out_matrix[i][j*DW +: DW])};
      row = {row, "]"};
      `uvm_info("PREDICTOR", row, UVM_MEDIUM)
    end

    // Send expected output to scoreboard
    pred_ap.write(output_tx);
  endfunction: write

endclass: predictor
 