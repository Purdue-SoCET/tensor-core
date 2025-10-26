// Does not actually simulate systolic array, 
// just a simple 3-stage pipeline for simulating 
// calculation time of systolic array

module simple_systolic_model (
    input logic CLK, nRST, output_ready,
    output logic output_valid, 
    output logic [511:0] output_data
);

    // simulate a 3 stage pipeline
    logic [2:0] valid;
    logic [511:0] data;

    always_comb begin
        valid[0] = output_ready;

        output_valid = valid[2];
        if (valid[2]) begin
            output_data = data;
        end else begin
            output_data = '0;
        end
    end

    always_ff @(posedge CLK or negedge nRST) begin
        if (!nRST) begin
            valid[1] <= 1'b0;
            valid[2] <= 1'b0;
            data <= '0;
        end else begin
            valid[1] <= valid[0];
            valid[2] <= valid[1];
            data <= $random;
        end
    end


    
endmodule