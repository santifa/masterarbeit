#!/usr/bin/env bash
#
# This script assembles the commands to build velisarios.
# Build on: Linux naglfar 5.0.13-arch1-1-ARCH #1 SMP PREEMPT x86_64 GNU/Linux


branch="raft"
opam="$(which opam)"
coq="$(which coq)"

if [[ -z "$opam" ]]; then
    echo "Opam not found; Aborting..."
    exit 1
fi

# test and switch to opam velisarios branch
cd Velisarios
velisarios="$(opam switch)"
if [[ "$velisarios" = *"velisarios"* ]]; then
    echo "Opam switch found..."
    opam switch velisarios
else
    echo "Create opam switch..."
    opam switch create velisarios ocaml-base-compiler.4.05.0
fi

if [[ -z "$coq" ]]; then
    echo "Installing COQ..."
    opam update
    opam pin add coq 8.7.2
    opam install coq
else
    echo "COQ found..."
fi

# now prepare the repository
git checkout $branch 2>/dev/null || git checkout -b $branch
echo "Create velisarios makefile..."
./create_makefile.sh
echo "Build the pdbft protocol..."
make -j 4 # assume at least 4 cores

echo "Install runtime deps..."
opam repo add janestreet https://ocaml.janestreet.com/opam-repository
opam install async ppx_jane core_extended rpc_parallel batteries cppo_ocamlbuild

echo "Install fixed nocrypto..."
cd ../ocaml-nocrypto
git checkout 1c4fb7aaefcd9bd78dc6f7c53906eafcd7f94496
opam install cstruct-lwt cstruct-unix ounit
sed -i s/Sexplib.Sexp.t/Ppx_sexp_conv_lib.Sexp.t/g src/nocrypto.mli
./pkg/pkg.ml build --with-unix true --with-lwt true --xen false --freestanding false
opam pin add nocrypto . -n
opam install nocrypto --verbose
# cstruct.lwt wird aktuell nicht gefunden

cd ..
echo "Build runtime..."
cd runtime
make ext
make

