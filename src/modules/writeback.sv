module writeback(
    writeback_if.wb wbif
);
    import cpu_types::*;

    always_comb begin
        wbif.wb_data = wbif.alu_out;

        if (wbif.wb_select) begin
            wbif.wb_data = wbif.store_out;
        end
    end
endmodule