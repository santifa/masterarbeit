
# Raft with Velisarios

This folder contains the code implementing the raft protocol with the velisarios framework.
Since Velisarios is provided as bunch of Vernacular files these are copied from the original
[repository](https://github.com/vrahli/Velisarios).

The folder is structured as follows:

     .
     ├── coq-tools - some usefull coq definitions
     ├── protocols - the protocol definitions in coq
     │   ├── PBFT - pbft impl
     │   ├── PrimaryBackup - a basic replication protocol
     │   ├── Raft - raft impl
     │   └── TwoThirds - two thirds census impl
     ├── simulator - the ocaml wrapper impls to run the protocols
     │   ├── lib - components used by all wrappers
     │   ├── pb - primary backup simulator
     │   ├── pbft - simulator, client, server
     │   └── raft - raft simulator
     └── velisarios - the main velisarios lib

There are multiple `_CoqProject` files scattered through the project which
helps the coqc interpreter to load correct qualifiers for imports. 

## Usage

The simulator has its own makefile to compile the wrappers but beforehand compile
the protocols.

Within the masterarbeit.org file is some piece of code to generate `Api.md` files with
the definitions from the coq files. 

To run the protocols see `simulator/README.md`.

### Installation

After a fresh copy create the makefile with `$ ./create_makefile.sh`.
Afterwards compile everything with `$ make` oder just some protocol with e.g.
`$ make protocols/PrimaryBackup/PrimaryBackup.vo`.

If something got changed either recompile with make oder use `$ make clean` to
remove all compiled files. Be aware that the compilation process may take several hours.
