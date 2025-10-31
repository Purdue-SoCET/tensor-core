//---------------------------------------------
// seq_in: Defines the transaction (sequence item)
//---------------------------------------------
class seq_in extends uvm_sequence_item;
  `uvm_object_utils(seq_in) // Register with the UVM factory for create()/print()/copy()

  // --------------------------------------------
  // Transaction fields (randomizable by default)
  // --------------------------------------------
  rand bit [31:0] addr;  // Address for read/write operation
  rand bit [31:0] data;  // Data to be written or read
  rand bit        write; // 1 = write transaction, 0 = read transaction

  // --------------------------------------------
  // Constructor
  // --------------------------------------------
  function new(string name = "seq_in");
    super.new(name);
  endfunction

  // --------------------------------------------
  // Convert item fields to a printable string
  // Useful for logging and debugging
  // --------------------------------------------
  function string convert2string();
    return $sformatf("addr=0x%0h data=0x%0h write=%0b", addr, data, write);
  endfunction
endclass



//---------------------------------------------
// basic_seq: Defines a simple sequence that sends one transaction
//---------------------------------------------
class basic_seq extends uvm_sequence #(seq_in);
  `uvm_object_utils(basic_seq) // Register with UVM factory

  // --------------------------------------------
  // Constructor
  // --------------------------------------------
  function new(string name = "basic_seq");
    super.new(name);
  endfunction

  // --------------------------------------------
  // Main sequence body
  // This is where the actual stimulus generation happens
  // --------------------------------------------
  virtual task body();
    seq_in req; // Declare a handle for the request item

    // Print info message when sequence starts
    `uvm_info(get_type_name(), "Starting basic_seq...", UVM_MEDIUM)

    // Create a new sequence item using the factory
    req = seq_in::type_id::create("req");

    // Assign specific values to the transaction fields
    req.addr  = 32'h1000;       // Target address
    req.data  = 32'hDEADBEEF;   // Write data
    req.write = 1'b1;           // Indicate write transaction

    // --------------------------------------------
    // Send the item to the driver via sequencer
    // --------------------------------------------
    start_item(req);   // Handshake: request driver to get ready
    finish_item(req);  // Send item data to the driver

    // Log transaction details after completion
    `uvm_info(get_type_name(), {"basic_seq completed: ", req.convert2string()}, UVM_LOW)
  endtask


  // --------------------------------------------
  // Static helper task for convenience
  // Allows starting this sequence directly on a sequencer
  // Example: basic_seq::send(my_seqr);
  // --------------------------------------------
  static task send(uvm_sequencer #(seq_in) seqr);
    basic_seq seq;
    seq = basic_seq::type_id::create("seq");
    seq.start(seqr); // Run the sequence on the provided sequencer
  endtask
endclass
