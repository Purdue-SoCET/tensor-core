// ReLu Activation Function
// Will be outside of the systolic array AFTER all MAC tiles are computed
// Function is called after neural network calculations are completed (inputs * weight + bias)

`timescale 1ns / 1ps

module ReLu #(parameter BITS = 16)
(
  input logic relu_enable,
  input logic signed [BITS-1:0] mac_out,
  output logic [BITS-1:0] relu_out
);

  always_comb begin
    relu_out = '0;

    if (relu_enable) begin
      if (mac_out [BITS - 1]) begin //check msb if 1, then negative
          relu_out = '0; 
      end
      else begin
        relu_out = mac_out;
      end
    end
  end

endmodule