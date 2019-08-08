
# Master thesis

This repository contains my master thesis about "Implementing RAFT with Velisarios".
[Velisarios](https://github.com/vrahli/Velisarios) is an implementation of the 
["Logic of Events"](http://www.nuprl.org/documents/Bickford/TechReportCLEinCTT.pdf)
within the proof management system [COQ](https://coq.inria.fr/). It is designed to implement and proof
distributed algorithm which are tendious and hard to program and test. This approach tries to
utilize these mechanism to implement the [RAFT](https://raft.github.io) census protocol. It aims
to be easier to understand then similar protocols like [Paxos](https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf)
and also easier to implement.

The goal is to produce an implementation using Velisarios and COQ which is runnable, stable and robust.

## Using this repository

Since this is my master thesis this repository is in a wip state until I'm finished.  
Note: The used literature is not provided alongside.  

### Prerequisites

The following tools are needed to interact with this repository:

* emacs (for some documentation things)
* ocaml
* opam (opam init already run)

Checkout the repository with `git clone --recursive https://github.com/santifa/masterarbeit.git`.

    Structure:
    
    +--- Velisarios (as reference included)
    +--- latex (my not further documented thesis)
    +--- learn-coq (some basic coq files to get a grasp in the language and system)
    +--- masterarbeit.org (personal notes, schedules, some code)
    +--- Makefile
    +--- bootstrap.sh (a shell script which assembles the commands I used to run velisarios)
    +--- raft (the code for my master thesis)

To get the code jump into the raft folder and dig to the readme files.

The Makefile contains only high level commands to convert the thesis and notes. 
Additional one can try to build velisarios but it is likely to not working.

Remark:  
The Velisarios submodule is added as reference. I copied the essential parts
to the raft folder as a velisarios package. Additionally I also copied the PBFT
and PrimaryBackup protocol as reference.

* `make schedule`: Just convert the org file into a pdf
* `make thesis`: Compile the thesis pdf
* `make velisarios`: Try to build velisarios
