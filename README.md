
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
    +--- latex (the written master thesis, not further documented)
    +--- learn-coq (scetches to get used to the COQ system)
    +--- masterarbeit.org (notes, schedules, some code)
    +--- Makefile
    +--- bootstrap.sh (assembles the commands needed to setup velisarios on arch linux)
    +--- raft (the actual source code for the examples and raft)



The Makefile contains the essentials to bootstrap the code
and build the documentation and thesis. The Velisarios module
is integrated for reference since the used code for raft is copied
from the project.

* `make schedule`: Just convert the org file into a pdf
* `make thesis`: Compile the thesis pdf
* `make velisarios`: Try to build velisarios

See the readme in the raft folder and the masterarbeit.org file for more information.
