`include "vector_if.vh"
 
 module vector_alu (
   vector_if.valu vif
 );
 
    always_comb begin
        // Special Cases

        // Normalize inputs
        

        casez (vif.vop)
            VALU_ADD: 

            default: v_if.result = '0;
        endcase
    end
 
 endmodule
