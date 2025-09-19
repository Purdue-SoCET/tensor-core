`include "fu_alu_if.vh"
`include "isa_types.vh"

module fu_alu(
    fu_alu_if.alu aluif
);
    import isa_pkg::*;

    logic sign_a;
    logic sign_b;

    assign sign_a = aluif.port_a[31];
    assign sign_b = aluif.port_b[31];

    always_comb begin : ALU_LOGIC
        aluif.overflow = 1'b0;
        aluif.port_output = 32'b0;
        if (aluif.enable) begin
            casez (aluif.aluop)
                ALU_SLL: aluif.port_output = aluif.port_a << aluif.port_b[4:0];
                ALU_SRL: aluif.port_output = aluif.port_a >> aluif.port_b[4:0];
                ALU_SRA: aluif.port_output = $signed(aluif.port_a) >>> aluif.port_b[4:0];
                ALU_ADD: begin
                    // Overflow occurs if signs are the same (e.g. large pos num + large pos num)
                    aluif.port_output = aluif.port_a + aluif.port_b;

                    if (sign_a == sign_b && aluif.port_output[31] != sign_a) begin
                        aluif.overflow = 1'b1;
                    end else begin
                        aluif.overflow = 1'b0;
                    end
                end
                ALU_SUB: begin
                    // Overflow occurs if signs are different (e.g. large neg num - large pos num)
                    aluif.port_output = aluif.port_a - aluif.port_b;

                    if (sign_a != sign_b && aluif.port_output[31] != sign_a) begin
                        aluif.overflow = 1'b1;
                    end else begin
                        aluif.overflow = 1'b0;
                    end
                end
                ALU_AND: aluif.port_output = aluif.port_a & aluif.port_b;
                ALU_OR: aluif.port_output = aluif.port_a | aluif.port_b;
                ALU_XOR: aluif.port_output = aluif.port_a ^ aluif.port_b;
                ALU_SLT: aluif.port_output = {31'b0, $signed(aluif.port_a) < $signed(aluif.port_b)};
                ALU_SLTU: aluif.port_output = {31'b0, aluif.port_a < aluif.port_b};
                default: aluif.port_output = '0;
            endcase
        end
    end

    assign aluif.negative = aluif.port_output[31];
    assign aluif.zero = (aluif.port_output == '0);
endmodule
