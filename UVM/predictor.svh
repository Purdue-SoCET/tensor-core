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

     foreach(t.input_matrix[i]) begin
        output_tx.out_matrix[i] = t.partial_matrix[i];
        for(int j=4; j>0; j--) begin
            for(int k=4; k>0; k--) begin
                output_tx.out_matrix[i][(j*16-1)-:16] += t.input_matrix[i][(k*16-1)-:16] * t.weight_matrix[k-1][(j*16-1)-:16];
                // $display("output_tx.out_matrix[%d][%d:%d] = %p", i, (j*16-1), (j*16-16), output_tx.out_matrix[i][(j*16-1)-:16]);
                // $display("t.input_matrix[%d][%d:%d] = %p", i, (k*16-1), (k*16-16), t.input_matrix[i][(k*16-1)-:16]);
                // $display("t.weight_matrix[%d][%d:%d] = %p", k-1, j*16-1, j*16-16, t.weight_matrix[k-1][(j*16-1)-:16]);
            end
        end
    end
    
    // send expected output to scoreboard
    pred_ap.write(output_tx);
  endfunction: write
endclass: predictor
