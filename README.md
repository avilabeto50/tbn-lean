# tbn-lean

An attempt at a Lean formalization of thermodynamic binding networks (TBNs).

This is a work in progress developed step by step. Some proofs still use
`sorry`, so a successful build does not mean the entire formalization has been
verified.

## Files

- `TBN/Basic.lean`: definitions of domains, monomers, systems, polymers, sites,
  bonds, matchings, configurations, and saturation.
- `TBN.lean`: the canonical example and its configuration, with proofs in progress.
- `Playground.lean`: space for experiments.

In this formalization, bonds between sites on the same monomer are forbidden.

## Setup

Install Lean's `elan` toolchain manager and, for editor support, the Lean 4
extension for VS Code. The project pins Lean and Mathlib to version 4.34.1.

```sh
git clone https://github.com/avilabeto50/tbn-lean.git
cd tbn-lean
lake exe cache get Mathlib.Data.Multiset.Basic Mathlib.Data.Finset.Basic
lake build
```

Open the `tbn-lean` folder in VS Code. If the editor was open during dependency
installation, restart the Lean server afterward.
