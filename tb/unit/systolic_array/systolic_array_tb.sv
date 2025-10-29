// 2-24-2025: changed to read in hex fp16's instead of ints from data input file

`include "systolic_array_if.vh"
`include "systolic_array_control_unit_if.vh"
`include "systolic_array_MAC_if.vh"
`include "systolic_array_add_if.vh"
`include "systolic_array_FIFO_if.vh"
`include "sys_arr_pkg.vh"
/* verilator lint_off IMPORTSTAR */
import sys_arr_pkg::*;
/* verilator lint_off IMPORTSTAR */
`timescale 1 ns / 1 ns

module systolic_array_tb();
  // clk/reset
  logic tb_nRST;

  string testcase = "fp";
  string path_to_files = "/home/vinay/tensorcore/tensor-core/";
  string input_filename = {"systolic_array_utils/matops_", testcase, "_encoded.txt"};
  string output_filename = {"systolic_array_utils/matops_", testcase, "_encoded_result.txt"};
  string python_output_filename = {"systolic_array_utils/matops_", testcase, "_encoded_output.txt"};
  string python_command = {"/bin/python3 ", path_to_files, "systolic_array_utils/matrix_mul_fp.py systolic_array_utils/matops_", testcase, "_encoded"};
  string comparison_command = {"/bin/python3 ", path_to_files, "systolic_array_utils/compare_sysarr_output.py systolic_array_utils/matops_", testcase, "_encoded_result.txt systolic_array_utils/matops_", testcase, "_encoded_output.txt systolic_array_utils/matops_", testcase, "_comp.txt"};

  // Memory interface instance
  systolic_array_if memory_if();

  // Clock gen
  parameter PERIOD = 10;
  logic tb_clk = 0;
  always #(PERIOD/2) tb_clk++;
  // FILE I/O
  int out_file, file, k, i, j, z, y, r, in, which;
  int sysarr_dump_file;
  /* verilator lint_off UNUSEDSIGNAL */
  string line;
  /* verilator lint_off UNUSEDSIGNAL */
  logic [DW-1:0] temp_weights[N][N];
  logic [DW-1:0] temp_inputs[N][N];
  logic [DW-1:0] temp_partials[N][N];
  logic [DW-1:0] temp_outputs[N][N];

  logic [(N*DW)-1:0] m_weights[N];
  logic [(N*DW)-1:0] m_inputs[N];
  logic [(N*DW)-1:0] m_partials[N];
  logic [(N*DW)-1:0] m_outputs[N];
  int loaded_weights;
  // Reset task
  task reset;
    begin
      tb_nRST = 1'b0;
      @(posedge tb_clk);
      @(posedge tb_clk);
      @(negedge tb_clk);
      tb_nRST = 1'b1;
      @(posedge tb_clk);
      @(posedge tb_clk);
    end
  endtask

  task row_load(
    input logic [1:0] rtype,
    input logic [$clog2(N)-1:0] rinnum,
    input logic [$clog2(N)-1:0] rpsnum,
    input logic [(N*DW)-1:0] rinput,
    input logic [(N*DW)-1:0] rpartial
  );
    begin
      if (rtype == 2'b00) begin
        memory_if.weight_en = 1'b1;
      end else if (|rtype) begin
        memory_if.input_en = rtype[0];
        memory_if.partial_en = rtype[1];
      end
      memory_if.row_in_en = rinnum;
      memory_if.row_ps_en = rpsnum;
      memory_if.array_in = rinput;
      memory_if.array_in_partials = rpartial;
      @(posedge tb_clk);
      memory_if.array_in = '0;
      memory_if.array_in_partials = '0;
      memory_if.weight_en = 1'b0;
      memory_if.partial_en = 1'b0;
      memory_if.input_en = 1'b0;
      memory_if.row_in_en = '0;
      memory_if.row_ps_en = '0;
    end
  endtask

  task get_matrices(output int weights);
    begin
      int iterations;
      $display("In get matrices task");
      weights = 0;
      which = 0;
      $fgets(line, file);
      // $display("In get matrices task. just fgets'ed");
      // $display("Line read in: %s", line);
      if (line == "Weights\n") begin
        which = 1;
        iterations = 3;
        weights = 1;
      end else if (line == "Inputs\n") begin
        which = 2;
        iterations = 2;
      end
      // $display("In get matrices task. just read value type. which: ");
      $display("%d", which);
      for (k = 0; k < iterations; k++) begin
        for (i = 0; i < N; i = i + 1) begin
          for (j = 0; j < N; j = j + 1) begin
            if (which == 1)begin
              $fscanf(file, "%x ", temp_weights[i][j]);
              // $display("i just read in weight %x", temp_weights[i][j]);
            end else if (which == 2) begin
              $fscanf(file, "%x ", temp_inputs[i][j]);
              // $display("i just read in input %x", temp_inputs[i][j]);
            end else begin
              $fscanf(file, "%x ", temp_partials[i][j]);
              // $display("i just read in partial %x", temp_partials[i][j]);
            end
          end  
        end
        which = which + 1;
        $fgets(line, file);
      end
      for (i = 0; i < N; i++)begin
        m_weights[i] = {>>{temp_weights[i]}};
        m_inputs[i] = {>>{temp_inputs[i]}};
        m_partials[i] = {>>{temp_partials[i]}};
      end
    end
  endtask

task get_m_output;
    begin
      for (i = 0; i < N; i = i + 1) begin
        for (j = 0; j < N; j = j + 1) begin
          $fscanf(out_file, "%x ", temp_outputs[i][N-1-j]);
        end
      end
      for (i = 0; i < N; i++)begin
        /* verilator lint_off WIDTHTRUNC */
        m_outputs[i] = {>>{temp_outputs[i]}};
        /* verilator lint_off WIDTHTRUNC */
      end
    end
  endtask

  task load_weights();
    for (r = N-1; r >= 0; r--)begin
      /* verilator lint_off WIDTHTRUNC */
      row_load(.rtype(2'b00), .rinnum(r), .rpsnum('0), .rinput(m_weights[r]), .rpartial('0));
      /* verilator lint_off WIDTHTRUNC */
    end
  endtask

  task load_in_ps(input int delay);
    for (in = 0; in < N; in++)begin
      /* verilator lint_off WIDTHTRUNC */
      row_load(.rtype(2'b11), .rinnum(in), .rpsnum(in), .rinput(m_inputs[in]), .rpartial(m_partials[in]));
      /* verilator lint_off WIDTHTRUNC */
      repeat(delay) @(posedge tb_clk); // everyone else iteration delay
    end
  endtask

  // Instantiate the DUT
  systolic_array DUT (
    .clk    (tb_clk),
    .nRST   (tb_nRST),
    .memory (memory_if.memory_array)
  );

  always @(posedge tb_clk) begin
    if (memory_if.out_en == 1'b1)begin
      $display("output row is %d", memory_if.row_out);
      if (m_outputs[memory_if.row_out] != memory_if.array_output)begin
        $display("Output incorrect\n");
        $display("Our Output is");
        for (y = 0; y < N; y++)begin
          $write("%x, ", memory_if.array_output[(y+1)*DW-1-:DW]);
        end
        $display("");
      end
      for (y = 0; y < N-1; y++)begin
          $fwrite(sysarr_dump_file, "%x ", memory_if.array_output[(y+1)*DW-1-:DW]);
      end
      $fwrite(sysarr_dump_file, "%x\n", memory_if.array_output[(N)*DW-1-:DW]);
      // $fwrite(sysarr_dump_file, "\n");
      $display("Correct Output is");
      for (z = 0; z < N; z++)begin
          $write("%x ", m_outputs[memory_if.row_out][(z+1)*DW-1-:DW]);
      end
      $display("");
      /* verilator lint_off WIDTHEXPAND */
      if (memory_if.row_out == N-1)begin
      /* verilator lint_off WIDTHEXPAND */
        get_m_output();
      end
    end
  end
  // Test Stimulus
   int flag;
  initial begin
    $dumpfile("dump.vcd");  // For VCD format
    $dumpvars(0, systolic_array_tb);
    memory_if.weight_en = '0;
    memory_if.input_en = '0;
    memory_if.partial_en = '0;
    memory_if.row_in_en = '0;
    memory_if.row_ps_en = '0;
    memory_if.array_in = '0;
    memory_if.array_in_partials = '0;
    loaded_weights = 0;
    
    // any file

    file = $fopen(input_filename, "r");
    $system(python_command);
    out_file = $fopen(python_output_filename, "r");
    sysarr_dump_file = $fopen(output_filename, "w");

    reset();
    get_matrices(.weights(loaded_weights));
    get_m_output();
    if (loaded_weights == 1)begin
      // LOAD WEIGHTS
      load_weights();
    end
    load_in_ps (.delay(1)); //delay was 1

    flag = 1;
    while (flag == 1) begin
      @(posedge tb_clk);
      if (memory_if.fifo_has_space == 1'b1)begin
        flag = 0;
      end
    end
    // repeat(N*N) @(posedge tb_clk); // last output drain
    get_matrices(.weights(loaded_weights));
    load_in_ps (.delay(1));
    flag = 1;
    while (flag == 1) begin
      @(posedge tb_clk);
      if (memory_if.drained == 1'b1)begin
        flag = 0;
      end
    end
    $display("array should be drained %d", memory_if.drained);
    $display("fifos should have space  %d", memory_if.fifo_has_space);

    get_matrices(.weights(loaded_weights));
    get_m_output();
    if (loaded_weights == 1)begin
      // LOAD WEIGHTS
      @(posedge tb_clk)           // Without this, fp6dub test case fails.
      load_weights();
    end
    load_in_ps (.delay(1)); //delay was 1

    flag = 1;
    while (flag == 1) begin
      @(posedge tb_clk);
      if (memory_if.drained == 1'b1)begin
        flag = 0;
      end
    end
    $display("array should be drained %d", memory_if.drained);
    $display("fifos should have space  %d", memory_if.fifo_has_space);
    
    $fclose(file);
    $fclose(out_file);
    $fclose(sysarr_dump_file);
    $system(comparison_command);

    #50;
    $stop;
  end

endmodule


