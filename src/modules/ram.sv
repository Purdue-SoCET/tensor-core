/*
Eric Villasenor
evillase@gmail.com
ram with variable latency
*/
// interface
`include "cpu_ram_if.vh"
// types
`include "cpu_types_pkg.vh"

module ram (input logic CLK, nRST, cpu_ram_if.ram ramif);
// import types
import cpu_types_pkg::*;
parameter BAD = 32'hBAD1BAD1, LAT = 0;
logic [3:0] count;
ramstate_t rstate;
word_t q, addr = 0;
logic wren;
logic [1:0] en;
altsyncram altsyncram_component (
.address_a (ramif.ramaddr[15:2]),
.clock0 (CLK),
.data_a (ramif.ramstore),
.wren_a (wren),
.q_a (q),
.aclr0 (1'b0),
.aclr1 (1'b0),
.address_b (1'b1),
.addressstall_a (1'b0),
.addressstall_b (1'b0),
.byteena_a (1'b1),
.byteena_b (1'b1),
.clock1 (1'b1),
.clocken0 (1'b1),
.clocken1 (1'b1),
.clocken2 (1'b1),
.clocken3 (1'b1),
.data_b (1'b1),
.eccstatus (),
.q_b (),
.rden_a (1'b1),
.rden_b (1'b1),
.wren_b (1'b0));
defparam
altsyncram_component.clock_enable_input_a = "BYPASS",
altsyncram_component.clock_enable_output_a = "BYPASS",
altsyncram_component.init_file = "meminit.hex",
altsyncram_component.intended_device_family = "Cyclone II",
altsyncram_component.lpm_hint =
"ENABLE_RUNTIME_MOD=YES,INSTANCE_NAME=RAM",
altsyncram_component.lpm_type = "altsyncram",
altsyncram_component.numwords_a = 16384,
altsyncram_component.operation_mode = "SINGLE_PORT",
altsyncram_component.outdata_aclr_a = "NONE",
altsyncram_component.outdata_reg_a = "UNREGISTERED",
altsyncram_component.power_up_uninitialized = "FALSE",
altsyncram_component.widthad_a = 14,
altsyncram_component.width_a = 32,
altsyncram_component.width_byteena_a = 1;
assign ramif.ramload = (rstate == ACCESS) ? q : BAD;
assign wren = (rstate == ACCESS) ? ramif.ramWEN : 0;
assign ramif.ramstate = rstate;
always_ff @(posedge CLK, negedge nRST)
begin
if (!nRST)
begin
count <= 0;
addr <= 0;
en <= 3;
end
else if (!(ramif.ramREN || ramif.ramWEN) || ramif.ramaddr != addr || en != {ramif.ramREN, ramif.ramWEN})
begin
en <= {ramif.ramREN, ramif.ramWEN};
count <= 0;
addr <= ramif.ramaddr;
end
else if ((ramif.ramREN || ramif.ramWEN) && count < LAT)
begin
count <= count + 1;
end
end
always_comb
begin
casez({ramif.ramWEN,ramif.ramREN,nRST})
3'b00z: rstate = FREE;
3'b011,
3'b101: rstate = BUSY;
default: rstate = ERROR;
endcase
if (!nRST || ((addr == ramif.ramaddr) && ((ramif.ramREN ||
ramif.ramWEN) && (count >= LAT))))
begin
rstate = ACCESS;
end
end
endmodule