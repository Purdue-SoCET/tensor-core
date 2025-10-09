
class lfc_environment extends uvm_env;
  `uvm_component_utils(lfc_environment)

  // Agents
  lfc_cpu_active_agent   cpu_active_ag;
  lfc_cpu_passive_agent  cpu_passive_ag;
  lfc_ram_active_agent   ram_active_ag;
  lfc_ram_passive_agent  ram_passive_ag;

  // Predictor & Scoreboard
  lfc_predictor      pred;
  lfc_scoreboard     sb;

  // Create components
  cpu_active_ag  = lfc_cpu_active_agent ::type_id::create("cpu_active_ag",  this);
  cpu_passive_ag = lfc_cpu_passive_agent::type_id::create("cpu_passive_ag", this);
  ram_active_ag  = lfc_ram_active_agent ::type_id::create("ram_active_ag",  this);
  ram_passive_ag = lfc_ram_passive_agent::type_id::create("ram_passive_ag", this);

  pred = lfc_predictor ::type_id::create("pred", this);
  sb   = lfc_scoreboard::type_id::create("sb",   this);

endclass
