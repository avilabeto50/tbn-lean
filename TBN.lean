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


def configA : TBNs.Configuration system where
  polymers := {⟨{m1, m2, m3}, by decide⟩, ⟨{m4}, by decide⟩}
  valid_monomers := by
    intro P P_in_config m m_in_P
    simp at P_in_config
    rcases P_in_config with first_polymer | second_polymer <;> subst P
    · simp at m_in_P
      rcases m_in_P with m1_in_P | m2_in_P | m3_in_P <;>
      subst m <;> simp [system]
    · simp at m_in_P
      subst m
      simp [system]


  all_monomers_assigned := by
    intro m m_in_system
    simp [system] at m_in_system
    rcases m_in_system with m1_in_system | m2_in_system | m3_in_system | m4_in_system <;> subst m
    · exact ⟨⟨{m1, m2, m3}, by decide⟩, by simp, by simp⟩
    · exact ⟨⟨{m1, m2, m3}, by decide⟩, by simp, by simp⟩
    · exact ⟨⟨{m1, m2, m3}, by decide⟩, by simp, by simp⟩
    · exact ⟨⟨{m4}, by decide⟩, by simp, by simp⟩

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
    by_cases p : P = ⟨{m1, m2, m3}, by decide⟩
    · subst P
      exact
        { bonds := {bondA, bondB}
          within_polymer := by
            intro b b_in_bonds
            simp at b_in_bonds
            rcases b_in_bonds with bondA_in_bonds | bondB_in_bonds
            · subst b
              simp [bondA]
            · subst b
              simp [bondB]
          unique_sites := by
            intro b₁ b₁_in_bonds b₂ b₂_in_bonds unique
            simp at b₁_in_bonds b₂_in_bonds
            rcases b₁_in_bonds with bondA_in_bonds | bondB_in_bonds <;>
              rcases b₂_in_bonds with bondA_in_bonds | bondB_in_bonds <;>
              subst b₁ <;> subst b₂
            · rfl
            · rcases unique with h | h | h | h
              · have bad := congrArg (fun s => s.monomer.id) h
                contradiction
              · have bad := congrArg (fun s => s.monomer.id) h
                contradiction
              · have bad := congrArg (fun s => s.monomer.id) h
                contradiction
              · have bad := congrArg (fun s => s.domain.name) h
                contradiction
            · rcases unique with h | h | h | h
              · have bad := congrArg (fun s => s.monomer.id) h
                contradiction
              · have bad := congrArg (fun s => s.monomer.id) h
                contradiction
              · have bad := congrArg (fun s => s.monomer.id) h
                contradiction
              · have bad := congrArg (fun s => s.domain.name) h
                contradiction
            · rfl
          no_exposed_complements := by
            intro s₁ s₂ s₁_in_P s₂_in_P s₁_ne_s₂ s₁_domain_eq_s₂_complement
            simp at s₁_in_P s₂_in_P
            rcases s₁_in_P with m1_in_P | m2_in_P | m3_in_P
            · sorry
            · sorry
            · sorry
           }
    · sorry











end Canonical
