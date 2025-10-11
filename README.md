# Purdue SoCET - Atalla x01 

> **“Building the first fully open, end-to-end AI accelerator platform — by students, for researchers.”**
 

## Overview 

The Atalla x01 Project is a student-led initiative to design and implement a complete **AI Hardware-Software** stack -- from RTL to PyTorch integration. Unlike isolated academic prototypes, this project aims to become an open, reproducible, and research-grade infrastructure that unites all key accelerator components under one roof.

> This project is not just a course assignment — it is part of a long-term open-source effort to build a full-stack AI system.

## Repository Structure 

```
/docs/ -> Documentation of Arch, Contribution Guide, etc. 
/kernels/ 
/rtl/ 
    /include/ -> Headers. 
    /modules/ -> RTL Design.  
    /tests/ -> .sv Testbenches (QuestaSim). 
    /waves/ -> `.do` Waveform Scripts (QuestaSim). 
/scripts/ -> Scripts runnable on `asicfab`.  
/aihw-ppci-compiler/ -> PPCI Infra, adapted for Atalla SW Stack.
/AMP-Sim/ -> Cycle-Accurate Simulator of Atalla x01 in Python. 
/UVM_1.2/ -> UVM Core Libs. 
/LICENSE 
/Makefile  
```

> Note: Synthesis flows are NDA-protected, and SoCET students are required to reach out to their GTAs to get setup with Design-Flow's PD flows. 

## Misc. 

- We enforce high standards for our "Design Logs", logs where contributing members explain their design choices and micro-architectural details to ensure their work is reproducible. You can find them [here](https://github.com/Purdue-SoCET/aihw-design-logs). 