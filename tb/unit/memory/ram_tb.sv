
module ram_tb;
  // clock period
  parameter PERIOD = 10;

  // signals
  logic CLK = 1, nRST;

  logic [9:0] addr;
  logic [31:0] din;
  logic we;
  wire [31:0] dout;

  // clock
  always #(PERIOD/2) CLK++;

  cpu_ram_if                            prif ();

  ram RAM(CLK, nRST, prif);

  endmodule