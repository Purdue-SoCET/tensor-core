## Overview 

If you cloned the repository properly, and ran the setup scripts, you should be able to see "Flowkit" as a submodule. This is a repository compiled by the Design Flow team with a bunch of scripts/flows to help us use Genus and Innovus. It was initially a Cadence software, but it's adapted. 

### Goals 

You will use the following steps to compile each of your modules to get area and clock information. After this, look at the [Reports](#reports) step on how to format and store the reports that are generated. 

### Steps

> The following steps outline what to do. Search for `@AIHW` tag in each of the respective files to know where to add/edit stuff. 

0. Ensure you are in the `atallax01` branch. 
```
git submodule update --init --recursive
```

1. CREATE - /designs/cache/filelist.tcl
```
set listofdirs {}
lappend listofdirs "/home/asicfab/a/araviki/tensor-core/src/include"
set_db init_hdl_search_path $listofdirs

read_hdl -sv -define {NOIP SYNTHESIS} /home/asicfab/a/araviki/tensor-core/src/modules/cache_bank.sv
read_hdl -sv -define {NOIP SYNTHESIS} /home/asicfab/a/araviki/tensor-core/src/modules/cache_mshr_buffer.sv
read_hdl -sv -define {NOIP SYNTHESIS} /home/asicfab/a/araviki/tensor-core/src/modules/lockup_free_cache.sv
```

2. EDIT - /scripts/config/design_config.tcl: 
search for "# Read Verilog and elaborate.", and add this below
```
create_flow_step -name read_cache_hdl -owner design {
  source ./designs/cache/filelist.tcl
}

create_flow_step -name elaborate_cache -owner design {
  elaborate lockup_free_cache # replace with the name of your actual module
}
```

3. EDIT - scripts/flow.yaml
search for "flow: synthesis:", near line 129
```
  synthesis:
    args: -tool genus -owner cadence -skip_metric -tool_options -disable_user_startup
    features:
    steps:
      - syn_generic:
          args: -owner cadence
          features:
          steps:
            - block_start:
            - init_elaborate:
            - init_design:
                args: -owner cadence
                features:
                steps:
                  - read_mmmc:
                  - read_physical:
                  # ########################
                  - read_cache_hdl: # replace this
                  - elaborate_cache: # replace this
                  # ########################
                  - read_power_intent:
                  - run_init_design:
                  - read_def:
                      enabled: "synth_ispatial || synth_hybrid"
```

4. CREATE - /scripts/constraints/cache_bank.sdc. Always have interfaces for your modules. If you say it doesn't need an interface, then that unit isn't worth synthesizing alone.
```
set sdc_version 2.0

set_units -capacitance 1.0fF
set_units -time 1.0ps

# Set the current design
current_design cache_bank

# -period sets time in ps, 1000 -> 1GHz, 5000 -> 200Mhz
# -waveform = {-period}/2
create_clock -name "clock1" -period 1000.0 -waveform {0.0 500.0} [get_ports <interface_instance_name>_clk]

set_clock_transition -rise 1 [get_clocks "clock1"]
set_clock_transition -fall 1 [get_clocks "clock1"]
set_clock_uncertainty 0.1 [get_clocks "clock1"]

set_clock_gating_check -setup 0.0

set_driving_cell -lib_cell inv_8x -pin X [ all_inputs ] -min -max
set_input_delay -add_delay 1.0 -clock [get_clocks clock1] [all_inputs -no_clocks] # simulate 1ps delay 
set_output_delay -add_delay 1.0 -clock [get_clocks clock1] [all_outputs]
```


5. EDIT - scripts/setup.yaml
search for "constraint_modes" near line 101 
```
constraint_modes:
  func:
    sdc_files:
      - scripts/constraints/cache_bank.sdc
```

6. RUN - 
```
# Takes a long time
flowtool -reset -to synthesis 

# Wakes up flowtool. It'll take a bit for all the required files to compile. You can run specific flow steps after this. 
flowtool -flow run_syn_opt -interactive_run -isolate step
report_timing -max_paths 10 -path_type full > critical_paths.txt
```

### Reports

Check within Flowkit/reports. `reports/syn_opt/` has the results from the optimal synthesized flow. `reports/syn_opt/qor.prt` has the important content. 
Create a folder for each submodule within `tensor-core/reports`, and store the relevant information in there. We will not gitignore it. 

1. To get the clock speed, take the {-period} value you set in /scripts/constraint/*.sdc file, and add the slack value. If clock period is (1000) and slack is (-555) then the clock speed = 1/(1555*10^-9)Hz 
2. To get the area, look under the Area section. Values are in (um)^2.