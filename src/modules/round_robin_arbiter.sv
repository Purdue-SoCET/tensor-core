module round_roubin_arbiter(
    input logic CLK,
    input logic nRST,
    input logic [2:0] request,
    output logic [2:0] req_out
);
    logic [2:0] mask, nmask;
    logic [2:0] maskedReq;
    logic [2:0] maskGrant, unmaskGrant;

    maskedReq = request & mask;

    //This is if 1 request;
    arbiter u0 (.req(request), .grant(unmaskGrant));

    arbiter u1 (.req(maskedReq), .grant(maskGrant));

    assign req_out = (maskedReq == 0) unmaskGrant : maskGrant;

    always_ff @(posedge CLK, negedge nRST) begin
        if (!nRST) begin
            mask <= 0;
        end else begin
            mask <= nmask;
        end
    end

    always_comb begin
        if (req_out == 0) begin
            nmask = mask;
        end else begin
            nmask = '1;
            for (int i = 0; i < 3; i++) begin
                nmask = 0;
                if (req_out[i]) break;
            end
        end
    end

endmodule


//Creating a priority arbiter
module #(
    parameter NUM_REQ = 3;
)arbiter (
    input logic [NUM_REQ - 1:0] req,
    output logic [NUM_REQ - 1:0] grant
);
    always_comb begin
        grant = 0;
        for (int i = 0; i < NUM_REQ; i++) begin
            if (req[i]) begin
                grant[i] = 1'b1;
                break;
            end
        end
    end

endmodule