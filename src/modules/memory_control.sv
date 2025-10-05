// FROM 437

`include "ram_pkg.vh"
`include "cache_control_if.vh"

module memory_control (
  input CLK, nRST,
  cache_control_if.cc ccif
);

    import ram_pkg::*;
  
  //ram outputs
  assign ccif.ramstore = ccif.dstore;
  assign ccif.ramaddr = ((ccif.dREN == 1) || (ccif.dWEN == 1)) ? ccif.daddr : ccif.iaddr;
  assign ccif.ramWEN = ccif.dWEN;
  assign ccif.ramREN = (((ccif.dREN == 1) || (ccif.iREN == 1))&&(ccif.dWEN != 1)) ? 1 : 0; //not sure
  
  //cache outputs
  assign ccif.iload = (ccif.iREN) ? (ccif.ramload) : '0; //'not sure
  assign ccif.dload = (ccif.ramload); //not sure
  assign ccif.iwait = (ccif.ramstate == ACCESS) ? (((ccif.iREN == 1) && (ccif.dWEN != 1) && (ccif.dREN != 1)) ? 0 : 1):1;
  assign ccif.dwait = (ccif.ramstate == ACCESS) ? ((ccif.dREN)? 0 : ((ccif.dWEN) ? 0 : 1)):1;

endmodule