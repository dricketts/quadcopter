Modular Deductive Verification of Sampled-Data Systems
==========

This repository contains the code related to the EMSOFT '16 paper "Modular Deductive Verification of Sampled-Data Systems". The sections below describe the dependencies needed to build this repository. Once these dependencies are installed, simply run ```make``` in the root directory.

Directory Structure
-------------------
This project contains three directories:

1. logic - our embedding of LTL, proof rules, automation, and some arithmetic facts
2. examples - our Sys abstraction and proof rules for our Sys and System abstractions (System.v) as well as various systems specified and verified using Sys. The proof rules for progress and preservation reside in examples/System.v.
3. model-checking - the models that we ran through PHAVer, dReach, and Flow*.

Dependencies
------------

You will need csdp:
```
apt-get install coinor-csdp
```

And you will need Z3, which you can get here:

[[https://github.com/Z3Prover/z3/releases]]

Coq Dependencies
----------------

This development uses Coq 8.5. All of the Coq dependencies, along with Coq itself, can be installed using OPAM [[http://coq.io/opam/get_started.html]]. You must install the following packages from Coq OPAM:

- coq-ext-lib
- coq-charge-core
- coq-smt-check
