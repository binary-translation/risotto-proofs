# Risotto: Architecture Mapping Proofs

Proofs for translating memory instructions between different CPU architectures, written in [Agda](https://agda.readthedocs.io/). For the paper "Risotto: A Dynamic Binary Translator for Weak Memory Model Architectures"


## Running/Checking

* [Install Agda (v.2.6.2)](https://agda.readthedocs.io/en/v2.6.2/getting-started/installation.html) with its standard library
* Make sure Agda can find the standard library (see the `~/.agda/libraries` and `~/.agda/defaults` files in the installation instructions)

> :warning: The proofs were developed with standard library version 1.7.1. Other versions may be incompatible.

There are multiple ways of type-checking the proofs; Two are listed below.


### Running/Checking: Command Line

The easiest way of checking the proofs is through a terminal.

* Run `agda src/Main.agda --safe`.

Once a proof type-checks, it's correct. Also check the "Code Navigation" section below to understand *what* it is proving.


### Running/Checking: Emacs

Another way of checking the proofs is with the `agda-mode` in Emacs.

* Install [Emacs](https://www.gnu.org/software/emacs/)
* Install `agda-mode` as described in Agda's install instructions (above).
* Load an `.agda` file in Emacs, and press `C-c C-l` to type-check the file.

If a proof type-checks, it's correct. Also check the "Code Navigation" section below to understand *what* it is proving.


## Code Navigation

The proofs consists of several parts (in `src/`):

* `Main.agda` - Links to all proofs
* `Arch/` - Memory model specifications for architectures
  * `General/` - A general specification of an execution in the axiomatic model. This is instantiated by the individual architectures (below).
  * `Armv8.agda` - The "Armed Cats" Armv8 model, with our proposed change
  * `X86.agda` - The X86 model
  * `TCG.agda` - Our TCG model
* `Map*to*.agda` - The *specification* of mapping executions between architectures (see section **(2.1)**)
* `Transform*.agda` - The *specificaton* of elimination and reordering transformations on TCG (see section **(2.1)**)
* `Proof/` - Contains all the proofs (also referenced by `Main.agda`)
  * `Framework.agda` - A general framework for memory model proofs
  * `Mapping/` - The mapping proofs between architectures (see section **(2.1)**)
    * `Framework.agda` - A framework for architecture-mapping proofs. Extends the general framework
  * `Elimination/` - Elimination proofs (see section **(2.1)**)
  * `Reorder/` - Reordering proofs (see section **(2.1)**)
