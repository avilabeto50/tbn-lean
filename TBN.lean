import TBN.Basic


namespace Canonical

def a : TBNs.Domain := ⟨'a', false⟩
def aStar : TBNs.Domain := ⟨'a', true⟩
def b : TBNs.Domain := ⟨'b', false⟩
def bStar : TBNs.Domain := ⟨'b', true⟩

def m1 : TBNs.Monomer := ⟨1, {a}⟩
def m2 : TBNs.Monomer := ⟨2, {b}⟩
def m3 : TBNs.Monomer := ⟨3, {aStar, bStar}⟩
def m4 : TBNs.Monomer := ⟨4, {a, b}⟩

def bondA : TBNs.Bond where
  site1 :=
    { monomer := m1
      domain := a
      id := ⟨0, by decide⟩ }
  site2 :=
    { monomer := m3
      domain := aStar
      id := ⟨0, by decide⟩ }
  valid := by decide

def bondB : TBNs.Bond where
  site1 :=
    { monomer := m2
      domain := b
      id := ⟨0, by decide⟩ }
  site2 :=
    { monomer := m3
      domain := bStar
      id := ⟨0, by decide⟩ }
  valid := by decide

def system : TBNs.TBN where
  monomers := {m1, m2, m3, m4}
  unique_monomers := by decide

def p123 : TBNs.Polymer where
  monomers := {m1, m2, m3}
  nonempty := by decide

def p4 : TBNs.Polymer where
  monomers := {m4}
  nonempty := by decide

def configA : TBNs.Configuration system where
  polymers := {p123, p4}
  valid_monomers := by
    intro P P_in_config m m_in_P
    simp at P_in_config
    rcases P_in_config with first_polymer | second_polymer <;> subst P
    · simp [p123] at m_in_P
      rcases m_in_P with m1_in_P | m2_in_P | m3_in_P <;>
      subst m <;> simp [system]
    · simp [p4] at m_in_P
      subst m
      simp [system]


  all_monomers_assigned := by
    intro m m_in_system
    simp [system] at m_in_system
    rcases m_in_system with h | h | h | h <;> subst m
    · exact ⟨p123, by simp, by simp [p123]⟩
    · exact ⟨p123, by simp, by simp [p123]⟩
    · exact ⟨p123, by simp, by simp [p123]⟩
    · exact ⟨p4, by simp, by simp [p4]⟩

  no_sharing := by
    intro P P_in_config Q Q_in_config P_ne_Q
    simp at P_in_config Q_in_config
    rcases P_in_config with first_polymer | second_polymer <;>
      rcases Q_in_config with first_polymer | second_polymer <;>
      subst P <;> subst Q
    · exact (P_ne_Q rfl).elim
    · change Disjoint ({m1, m2, m3} : Finset TBNs.Monomer) {m4}
      decide
    · change Disjoint ({m4} : Finset TBNs.Monomer) {m1, m2, m3}
      decide
    · exact (P_ne_Q rfl).elim

  matching := by
    intro P P_in_config
    simp at P_in_config
    by_cases first_polymer : P = (p123 : TBNs.Polymer)
    · subst P
      exact  {
        bonds := {bondA, bondB}
        within_polymer := by
          { intro b b_in_bonds
            simp at b_in_bonds
            rcases b_in_bonds with bond1 | bond2 <;>
              subst b <;>
              simp [bondA, bondB, p123]
          }
        unique_sites := by
          { intro b₁ b₁_in_bonds b₂ b₂_in_bonds shared_site
            simp at b₁_in_bonds b₂_in_bonds
            rcases b₁_in_bonds with h₁ | h₁ <;>
              rcases b₂_in_bonds with h₂ | h₂ <;>
              subst b₁ <;> subst b₂
            · rfl
            · rcases shared_site with h | h | h | h <;>
              simp [bondA, bondB, m1, m2, m3, a, aStar, b, bStar] at h
            · rcases shared_site with h | h | h | h <;>
              simp [bondA, bondB, m1, m2, m3, a, aStar, b, bStar] at h
            · rfl
              }
        --- AI Generated
        no_exposed_complements := by
          intro s₁ s₂ s₁_in_P s₂_in_P s₁_ne_s₂
            s₁_eq_s2_complement both_exposed
          rcases both_exposed with ⟨s₁_exposed, s₂_exposed⟩

          -- Unpack the first site.
          rcases s₁ with ⟨owner, d, i⟩

          -- Its index guarantees that its domain occurs on its owner.
          have domain_present : d ∈ owner.domains :=
            Multiset.count_pos.mp
              (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)

          simp [p123] at s₁_in_P
          rcases s₁_in_P with on_m1 | on_m2 | on_m3

          · subst owner
            simp [m1] at domain_present
            subst d

            have index_zero : i.val = 0 := by
              have bound := i.isLt
              change i.val < 1 at bound
              omega
            have index_eq : i = ⟨0, by decide⟩ :=
              Fin.ext index_zero
            subst i

            -- This site is bondA's first endpoint.
            exact (s₁_exposed bondA (by simp)).1 rfl

          · subst owner
            simp [m2] at domain_present
            subst d

            have index_zero : i.val = 0 := by
              have bound := i.isLt
              change i.val < 1 at bound
              omega
            have index_eq : i = ⟨0, by decide⟩ :=
              Fin.ext index_zero
            subst i

            -- This site is bondB's first endpoint.
            exact (s₁_exposed bondB (by simp)).1 rfl

          · subst owner
            simp [m3] at domain_present
            rcases domain_present with is_aStar | is_bStar

            · subst d
              have index_zero : i.val = 0 := by
                have bound := i.isLt
                change i.val < 1 at bound
                omega
              have index_eq : i = ⟨0, by decide⟩ :=
                Fin.ext index_zero
              subst i

              -- This site is bondA's second endpoint.
              exact (s₁_exposed bondA (by simp)).2 rfl

            · subst d
              have index_zero : i.val = 0 := by
                have bound := i.isLt
                change i.val < 1 at bound
                omega
              have index_eq : i = ⟨0, by decide⟩ :=
                Fin.ext index_zero
              subst i

              -- This site is bondB's second endpoint.
              exact (s₁_exposed bondB (by simp)).2 rfl
      }
    · have second_polymer : P = (p4 : TBNs.Polymer) := by
        exact P_in_config.resolve_left first_polymer
      subst P
      exact {
        bonds := ∅

        within_polymer := by
          intro b b_in_bonds
          simp at b_in_bonds

        unique_sites := by
          intro b₁ b₁_in_bonds
          simp at b₁_in_bonds

        no_exposed_complements := by
          intro s₁ s₂ s₁_in_P s₂_in_P different_owners
          simp [p4] at s₁_in_P s₂_in_P
          exact (different_owners
            (s₁_in_P.trans s₂_in_P.symm)).elim
    }


--- AI GENERATED
theorem configAIsSaturted : TBNs.Configuration.Saturated (configA) := by
  unfold TBNs.Configuration.Saturated
  intro P P_in_config Q Q_in_config P_ne_Q s₁ s₂ s₁_in_P s₂_in_P s₁_eq_s₂_complement both_exposed
  rcases both_exposed with ⟨s₁_exposed, s₂_exposed⟩
  simp [configA] at P_in_config Q_in_config
  have no_exposed_in_p123 :
      ∀ s : TBNs.Site,
        s.monomer ∈ p123.monomers →
        ¬ s.Exposed ({bondA, bondB} : Set TBNs.Bond) := by
    intro s s_in_P exposed
    rcases s with ⟨owner, d, i⟩

    -- A valid occurrence index means the domain is present.
    have domain_present : d ∈ owner.domains :=
      Multiset.count_pos.mp
        (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)

    -- Identify the owner, then its possible domains.
    simp [p123] at s_in_P
    rcases s_in_P with h | h | h <;>
      subst owner <;>
      simp [m1, m2, m3] at domain_present

    all_goals
      first
      | (rcases domain_present with rfl | rfl)

    -- Each of these domains occurs exactly once on its owner.
    all_goals
      have index_zero : i.val = 0 := by
        have bound := i.isLt
        change i.val < 1 at bound
        omega
      have index_eq : i = ⟨0, by decide⟩ :=
        Fin.ext index_zero
      subst i

      -- Each possible site is an endpoint of one of the bonds.
      first
      | exact (exposed bondA (by simp)).1 rfl
      | exact (exposed bondA (by simp)).2 rfl
      | exact (exposed bondB (by simp)).1 rfl
      | exact (exposed bondB (by simp)).2 rfl

  rcases P_in_config with p₁ | p₂ <;>
    rcases Q_in_config with q₁ | q₂ <;>
    subst P <;> subst Q

  · exact P_ne_Q rfl

  · apply no_exposed_in_p123 s₁ s₁_in_P
    simpa [configA] using s₁_exposed

  · apply no_exposed_in_p123 s₂ s₂_in_P
    simpa [configA] using s₂_exposed

  · exact P_ne_Q rfl


end Canonical
