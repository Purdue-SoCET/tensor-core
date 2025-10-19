
module flex_counter #( parameter N=4 ) (
    input logic nrst,
    input logic clk,
    input logic enable,
    output logic[0:N-1] count
);

always_ff @( posedge clk, negedge nrst ) begin
    if (~nrst) count <= '0;
    else count <= count + enable;
end


endmodule