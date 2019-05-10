
# Raft with Velisarios

This folder contains the code implementing the raft protocol with the velisarios framework.
Since Velisarios is provided as bunch of Vernacular files these are copied from the original
[repository](https://github.com/vrahli/Velisarios).

## Usage

### Installation

Create a makefile with `$ ./create_makefile.sh` and compile everything with `$ make`.
This process may fail and maybe is replaced with some more elaborate [makefile generation](https://github.com/DistributedComponents/coqproject).

The repository can be cleaned with `$ make clean`

### Structure

* `coq-tools`: Some useful tools for working with coq
* `velisarios`: The velisarios framework condesed into two folders
(Should be a module instead?)
* `src`: Example code and the code for the raft implementation

Currently the part for simulating a protocol with velisarios is missing.
Besides that, the file `Api.md` contains the Types and Signatures provided by
the folders with no claim of completness and accuracy.
