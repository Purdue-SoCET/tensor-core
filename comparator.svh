import uvm_pkg::*;
`include "uvm_macros.svh"

class comparator extends uvm_scoreboard;
  `uvm_component_utils(comparator)

  uvm_analysis_export#(transaction) expected_export; // to recieve result from predictor
  uvm_analysis_export#(transaction) actual_export; // to recieve result from DUT
  uvm_tlm_analysis_fifo#(transaction) expected_fifo;
  uvm_tlm_analysis_fifo#(transaction) actual_fifo;

  int m_matches, m_mismatches; // number of matches and mismatches

  function new(string name, uvm_component parent);
    super.new(name, parent);
    m_matches = 0;
    m_mismatches = 0;
  endfunction

  function void build_phase(uvm_phase phase);
    expected_export = new("expected_export", this);
    actual_export = new("actual_export", this);
    expected_fifo = new("expected_fifo", this);
    actual_fifo = new("actual_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    expected_export.connect(expected_fifo.analysis_export);
    actual_export.connect(actual_fifo.analysis_export);
  endfunction

  task run_phase(uvm_phase phase);
    transaction expected_tx;
    transaction actual_tx;
    forever begin
      expected_fifo.get(expected_tx);
      actual_fifo.get(actual_tx);
      // uvm_report_info("Comparator", $psprintf("\nExpected:\ndrained:%d\n fifo_has_space:%d\n row_out %d\n array_output %d\n out_en\n %d\n~~~~~~~~~~\nActual:\ndrained:%d\n fifo_has_space:%d\n row_out %d\n array_output %d\n out_en\n %d\n", expected_tx.drained, expected_tx.fifo_has_space, expected_tx.row_out, expected_tx.array_output, expected_tx.out_en, actual_tx.drained, actual_tx.fifo_has_space, actual_tx.row_out, actual_tx.array_output, actual_tx.out_en));
      uvm_report_info("Comparator", $psprintf("\nExpected:\narray_output %d\n ~~~~~~~~~~\nActual:\narray_output %d\n", expected_tx.array_output, actual_tx.array_output));
      // keep count of number of matches and mismatches (actual vs expected)
      if (expected_tx.compare(actual_tx)) begin
        m_matches++;
        uvm_report_info("Comparator", "Data match");
      end else begin
        m_mismatches++;
        uvm_report_info("Comparator", "Error: Data mismatch");
      end
    end
  endtask

  function void report_phase(uvm_phase phase);
    uvm_report_info("Comparator", $sformatf("Matches:    %0d", m_matches));
    uvm_report_info("Comparator", $sformatf("Mismatches: %0d", m_mismatches));
  endfunction
endclass
