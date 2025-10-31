
class seq_in extends uvm_sequence_item;
  `uvm_object_utils(seq_in)

  rand bit [31:0] addr;
  rand bit [31:0] data;
  rand bit        write; // 1 = write, 0 = read

  function new(string name = "seq_in");
    super.new(name);
  endfunction

  function string convert2string();
    return $sformatf("addr=0x%0h data=0x%0h write=%0b", addr, data, write);
  endfunction
endclass



class basic_seq extends uvm_sequence #(seq_in);
  `uvm_object_utils(basic_seq)
  
  function new(string name = "basic_seq");
    super.new(name);
  endfunction

  virtual task body();
    seq_in req;
    `uvm_info(get_type_name(), "Starting basic_seq...", UVM_MEDIUM)

    req = seq_in::type_id::create("req");

    req.addr  = 32'h1000;
    req.data  = 32'hDEADBEEF;
    req.write = 1'b1;

    start_item(req);
    finish_item(req);

    `uvm_info(get_type_name(), {"basic_seq completed: ", req.convert2string()}, UVM_LOW)
  endtask


  static task send(uvm_sequencer #(seq_in) seqr);
    basic_seq seq;
    seq = basic_seq::type_id::create("seq");
    seq.start(seqr);
  endtask
endclass
