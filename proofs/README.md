# Proofs

This repository contains the proof of the monotonicity of the set of deduction
rules implemented in ParTAGe.


# Usage

The proof is written using the Coq proof assistant, you will therefore need to
install it before you can verify the proofs. If you install `coqide`, you can
read and interactively edit a particular `FILE.v` using the following command:

    coqide -async-proofs off -async-proofs-command-error-resilience off FILE.v


# Compilation

Subsequent `.v` files rely on the preceding ones.  To make the makefile:

    ./make_makefile.sh

To compile all `.v` files to `.vo`:

    make

To compile a specific file, e.g., `Basics.v` to `Basics.vo`:

    make Basics.vo


# Structure

The two main files are:

  * `Grammar.v` -- states the assumptions on the weighted TAG grammar and its
    representation, the available grammar-related functions, etc.
  * `InfRules.v` -- defines the inference (deduction) rules of the parser and
    provides the proof of the monotonicity of the system.
