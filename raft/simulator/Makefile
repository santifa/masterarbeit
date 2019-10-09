#
# This makefile is used to extract the COQ code and build the demonstration cases,
# the benchmarks and tests.
# The default protocol is raft but others should be build by its name.
#

# ocaml flags
OCB_FLAGS = -tag bin_annot -tag thread -use-ocamlfind -Is pb,raft,pbft,lib -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix,yojson
OCB = ocamlbuild $(OCB_FLAGS)

# coq flags
COQ_PATH = -R ../coq-tools Tools -R ../velisarios Velisarios -R ../protocols Protocols -R . Simulator

LIB=$(lib/%.ml)

default: general raft

general: RsaKey.native

pbft: general pbft-ext PbftReplica.native PbftClient.native RsaKey.native PbftSimul.native

raft: general raft-ext general raft-tests raft-demonstrations

raft-tests: RaftTest.native RaftTestInit.native

raft-demonstrations: RaftClient.native RaftSimul.native RaftReplica.native

pb: general pb-ext PbTest.native PbSimul.native

### Extraction from coq ###
sim-ext: Simulator.v
	coqc $(COQ_PATH) $<

pb-ext: sim-ext
	coqc $(COQ_PATH) pb/PbSim.v
	mv PbReplicaEx.ml pb/
	mv PbReplicaEx.mli pb/

raft-ext: sim-ext
	coqc $(COQ_PATH) raft/RaftSim.v
	mv RaftReplicaEx.ml raft/
	mv RaftReplicaEx.mli raft/

pbft-ext: sim-ext
	coqc $(COQ_PATH) pbft/PBFTsim.v

### pb ###
PbSimul.native: pb/PbSimul.ml $(LIB)
	$(OCB) PbSimul.native

PbTest.native: pb/PbTest.ml $(LIB)
	$(OCB) pb/PbTest.native

### raft ###
RaftClient.native: raft/RaftClient.ml
	$(OCB) RaftClient.native
	mv RaftClient.native Client.native

RaftReplica.native:
	$(OCB) RaftReplica.native
	mv RaftReplica.native Replica.native

RaftSimul.native: raft/RaftSimul.ml
	$(OCB) RaftSimul.native

RaftTest.native: raft/RaftTest.ml
	$(OCB) RaftTest.native

RaftTestInit.native: raft/RaftTestInit.ml
	$(OCB) RaftTestInit.native

RaftTestElection.native: raft/RaftTestElection.ml
	$(OCB) RaftTestElection.native

### pbft ###
PbftReplica.native:
	$(OCB) PbftReplica.native
	mv PbftReplica.native Replica.native

PbftClient.native:
	$(OCB) PbftClient.native
	mv PbftClient.native Client.native

PbftSimul.native: pbft/PbftSimul.ml
	$(OCB) PbftSimul.native

PbftSimul2.native: pbft/PbftSimul2.ml
	$(OCB) PbftSimul2.native

### protocol agnostic parts ###
RsaKey.native:
	$(OCB) RsaKey.native


ext:
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds Simulator.v
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim.v

sext:
	(cd ..; make PBFT/PBFT.vo)
	(cd ..; make PBFT/PBFTcollision_resistant.vo)
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds Simulator.v
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim_mac.v

oldext:
	coqc -R ../coq-tools util -R ../model model -R ../PBFT PBFT -R ../PrimaryBackup PrimaryBackup -R ../runtime runtime -R ../TwoThirds TwoThirds PBFTsim.v

cleano:
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build

clean:
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat

cleana:
	rm -f *.cmo
	rm -f *.cmi
	rm -f *.cma
	rm -f *.native
	rm -f *.byte
	rm -f a.out
	rm -Rf _build
	rm -f PbftReplica*
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat
	rm -f private_key*
	rm -f public_key*
