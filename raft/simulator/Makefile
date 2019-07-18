

OCB_FLAGS = -tag bin_annot -tag thread -use-ocamlfind -Is pb,raft,pbft,lib -package ppx_jane,async,core_extended,batteries,rpc_parallel,nocrypto.unix
OCB = ocamlbuild $(OCB_FLAGS)

default: pbft

pbft: PbftReplica.native PbftClient.native RsaKey.native PbftSimul.native

raft: RaftClient.native RsaKey.native

pb: PbSimul.native

### pb ###
PbSimul.native: pb/PbSimul.ml
	$(OCB) PbSimul.native

### raft ###
RaftClient.native: raft/RaftClient.ml
	$(OCB) RaftClient.native
	mv RaftClient.native Client.ml

RaftReplica.native:
	$(OCB) RaftReplica.native
	mv RaftReplica.native Replica.native

RaftSimul.native: raft/RaftSimul.ml
	$(OCB) RaftSimul.native

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

sim-ext: Simulator.v
	coqc -R ../coq-tools Tools -R ../velisarios Velisarios -R ../protocols Protocols -R . Simulator Simulator.v

pb-ext: sim-ext
	coqc -R ../coq-tools Tools -R ../velisarios Velisarios \
	-R ../protocols Protocols -R . Simulator pb/PbSim.v

raft-ext: sim-ext
	coqc -R ../coq-tools Tools -R ../velisarios Velisarios \
	-R ../protocols Protocols -R . Simulator raft/RaftSim.v

pbft-ext: sim-ext
	coqc -R ../coq-tools Tools -R ../velisarios Velisarios -R ../protocols Protocols -R . Simulator pbft/PBFTsim.v

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
	rm -f PbftReplica*
	rm -f *.glob
	rm -f *.vo
	rm -f .*.aux
	rm -f *.dat
	rm -f private_key*
	rm -f public_key*
