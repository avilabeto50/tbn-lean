import Std
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic

namespace TBNs


structure Domain where
  name : Char
  starred : Bool
  deriving DecidableEq, Repr

def Domain.complement (d : Domain) : Domain :=
  { d with starred := !d.starred }

structure Monomer where
  id : Nat
  domains : Multiset Domain
  deriving DecidableEq

structure TBN where
  monomers : Multiset Monomer
  unique_monomers : (monomers.map Monomer.id).Nodup

structure Polymer where
  monomers : Finset Monomer
  nonempty : monomers.Nonempty
  deriving DecidableEq

structure Site where
  monomer : Monomer
  domain : Domain
  id : Fin (monomer.domains.count domain)

structure Bond where
  site1 : Site
  site2 : Site
  valid : site1.domain = site2.domain.complement
    ∧ site1.monomer ≠ site2.monomer

def Site.Exposed (s : Site) (bonds : Set Bond) : Prop :=
  ∀ b ∈ bonds, b.site1 ≠ s ∧ b.site2 ≠ s

structure BondMatching (P : Polymer) where
  bonds : Set Bond
  within_polymer : ∀ b ∈ bonds, b.site1.monomer ∈ P.monomers ∧ b.site2.monomer ∈ P.monomers
  unique_sites :
    ∀ b1 ∈ bonds, ∀ b2 ∈ bonds,
      (b1.site1 = b2.site1 ∨
      b1.site1 = b2.site2 ∨
      b1.site2 = b2.site1 ∨
      b1.site2 = b2.site2) →
      b1 = b2
  no_exposed_complements :
    ∀ s1 s2 : Site,
      s1.monomer ∈ P.monomers →
      s2.monomer ∈ P.monomers →
      s1.monomer ≠ s2.monomer →
      s1.domain = s2.domain.complement →
      ¬ (s1.Exposed bonds ∧ s2.Exposed bonds)

structure Configuration (T: TBN) where
  polymers : Finset Polymer

  valid_monomers :
    ∀ P ∈ polymers, ∀ m ∈ P.monomers, m ∈ T.monomers

  all_monomers_assigned :
    ∀ m ∈ T.monomers, ∃ P ∈ polymers, m ∈ P.monomers

  no_sharing :
    ∀ P ∈ polymers, ∀ Q ∈ polymers,
    P ≠ Q → Disjoint P.monomers Q.monomers

  matching:
    ∀ P ∈ polymers, BondMatching P


-- in progress
def Configuration.Saturated {T : TBN} (C : Configuration T) : Prop :=
  ∀ P (P_in_config : P ∈ C.polymers),
  ∀ Q (Q_in_config : Q ∈ C.polymers),
    P ≠ Q →
    ∀ s1 s2 : Site,
      s1.monomer ∈ P.monomers →
      s2.monomer ∈ Q.monomers →
      s1.domain = s2.domain.complement →
      ¬ (s1.Exposed (C.matching P P_in_config).bonds
        ∧ s2.Exposed (C.matching Q Q_in_config).bonds)




end TBNs
