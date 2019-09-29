
# Simulator / Runtime

This folder contains the simulator and runtime for
the protocols implemented with COQ and Velisarios.

## Building

In order to use this part be sure to compile the parent repository.
To use the runtime or simulator some more Ocaml packages are needed

    opam repo add janestreet https://ocaml.janestreet.com/opam-repository
    opam install async ppx_jane core_extended rpc_parallel batteries cppo_ocamlbuild


Afterwards run `make` and the raft code gets extracted from coq and compiled in ocaml.

## Structure

The `lib` directory contains general modules and the `Simulator.ml` which can be used to
implement a new simulator.

The test cases can be found under `$prot-tests` and run with `make $prot-tests`.
The same is true for the benchmarks.

At the moment three different protocols are implement in different states.
The primary backup (pb) demonstrates the connection between COQ and Ocaml.
The PBFT protocol shows the full implementation without the tests.
The Raft protocol trys to show the full implementation.


### Simulator

To set up a new simulator include and implement the simulator API.
The basic steps are:

    (* include module *)
    open Simulator
    
    (* implement the virtual simulator *)
    class ['a, 'b, 'c, 'd] pb c = object(self)
      (* pass the config c to the upper class *)
      inherit ['a, 'b, 'c, 'd] simulator c
    
     method msgs2string msgs : string =
     (* convert a list of messages to a printable representation *)
    
     method create_replicas =
     (* create the nodes *)
    
     method run_replicas inflight =
     (* handle request created in the client method *)
 
     method client responses =
     (* create some clients requests *)
    end
 
    let _ =
     (* create a new primary backup simulation *)
     let c = new pb {
       version = "1.0";
       protocol = "PB";
       client_id = 0;
       private_key = lookup_client_sending_key (Obj.magic 0);
       primary = Obj.magic PBprimary (* type: name *)
    } in
    c#run

See the `pb` folder for simple examples on how to use the simulator and the test classes.

---

Taken from the original README:

### Installation

We use Async to implement sender/receiver threads, and
[Nocrypto](http://mirleft.github.io/ocaml-nocrypto/doc/index.html) for
crypto stuff.  To install all that, run:

**Nocrypto seems to be broken at the moment**

### Usage Simulator 

- run "make ext" and then "make"
- run "./Simul.native -max XXX", where XXX is the number of requests
  to send

### Usage runtime

- run: ./run.sh

- Clients will produce data files (pbftX.dat) that can be plotted using:
    cp pbft_ts_X_R_C.dat pbft.dat; gnuplot script.p
    cp pbft_avg_X_R_C.dat pbft.dat; gnuplot script.p
  where X is the client id
        R is the number of replicas
	C is the number of clients
