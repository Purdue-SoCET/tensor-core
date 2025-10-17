`ifndef FRONTEND_VC_SV
`define FRONTEND_VC_SV

import scpad_pkg::*;

// Minimal frontend_vc placeholder
// - Accepts the full scpad_if interface as `vcif` and currently performs no
//   transformation. This keeps the frontend/frontend_vc integration well-formed
//   while the internal arbitration/edits are implemented later.
module frontend_vc #(
    parameter logic [SCPAD_ID_WIDTH-1:0] IDX = '0
) (
    // accept the full interface instance so callers may pass modport or
    // interface instances as appropriate
    scpad_if vcif
);

    // Currently no internal logic. Add arbitration, request/response
    // transformations, or per-unit editing here in future.

endmodule

`endif
