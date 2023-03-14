import Mathlib.Init.Algebra.Order

/-  disjunctive syllogism -/
theorem mtp {p q : Prop} (hpq: p ∨ q)(hnp: ¬ p):  q :=  by cases hpq ; contradiction ; assumption

----------------------

inductive FamilyMembers where | father | mother | son | daughter open FamilyMembers
inductive Roles where | Murderer | Victim | Witness | Accessory open Roles

variable { role: FamilyMembers → Roles }

------------------

inductive Sexes where | male | female open Sexes 

-- lemma eq_female_of_ne_male :∀ (s : Sexes) (_: s≠male),  s=female  | female, _ => rfl

def sex: FamilyMembers → Sexes
  | father => male
  | mother => female
  | son => male
  | daughter => female

-----------------

-- variable [LE FamilyMembers] [LT FamilyMembers]
variable [po:Preorder FamilyMembers]

variable { youngest oldest: FamilyMembers }
variable ( isYoungest: ∀ x, x ≠ youngest → youngest < x )
variable ( isOldest: ∀ x, x ≠ oldest → oldest > x )

axiom mother_older_then_children: mother > daughter ∧ mother > son

----------------------------------  
variable { murderer victim witness accessory: FamilyMembers }

variable ( isMurderer: role murderer = Murderer )
variable ( isVictim: role victim = Victim )
variable ( isWitness: role witness = Witness )
variable ( isAccessory: role accessory = Accessory )

variable ( a1: (sex accessory) ≠ (sex witness) ) #check @a1
variable ( a2: (sex oldest) ≠ (sex witness) ) #check @a2
variable ( a3: (sex youngest) ≠ (sex victim) ) #check @a3
variable ( a4: accessory > victim )  #check @a4
variable ( a5: oldest = father ) #check @a5
variable ( a6: murderer ≠ youngest ) #check @a6

-------------------------------
lemma W_is_Female: (sex witness) = female := by
  have h1: (sex father) ≠ (sex witness) := a5 ▸ a2
  have h2: (sex father) = male := rfl
  have h3: (sex witness) ≠ male := Ne.symm (h2 ▸ h1)
  
  cases witness
  . exact False.elim (h3 rfl) -- father
  . rfl -- mother
  . exact False.elim (h3 rfl) -- son
  . rfl -- daughter

lemma A_is_Male: (sex accessory) = male := by
  have h: (sex accessory) ≠ female:= ( W_is_Female isWitness a1 a2 a5 ) ▸ a1

  cases accessory
  . rfl
  . apply False.elim ; rw [sex] at h ; contradiction
  . rfl
  . apply False.elim ; rw [sex] at h ; contradiction

lemma MW_or_DW : witness=mother ∨ witness=daughter :=   by
  have h4: (sex witness) = female := W_is_Female isWitness a1 a2 a5

  cases witness
  · apply False.elim ; simp [sex] at h4
  · apply Or.inl ; rfl
  · apply False.elim ; simp [sex] at h4
  · apply Or.inr ; rfl

  -- have h1: (sex father) ≠ (sex witness) := a5 ▸ a2
  -- have h2: (sex father) = male := rfl
  -- have h3: (sex witness) ≠ male := Ne.symm (h2 ▸ h1)
  -- have h4: (sex witness) = female := eq_female_of_ne_male (sex witness) h3

  -- match witness with
  -- | mother => 
  --   have h : mother = mother := rfl
  --   show mother=mother ∨ mother=daughter from Or.inl h
  -- | daughter =>
  --   have h : daughter = daughter := rfl
  --   show daughter=mother ∨ daughter=daughter from Or.inr h
  -- | son => 
  --   have h1 : sex son = male := rfl
  --   have h2 : male ≠ female := Sexes.noConfusion -- or by simp
  --   have h3 := Eq.trans h1.symm ( W_is_Female isWitness a1 a2 a5 )  
  --   show son=mother ∨ son=daughter from absurd h3 h2
  -- | father => 
  --   have h1 : sex father = male := rfl
  --   have h2 : male ≠ female := Sexes.noConfusion -- or by simp
  --   have h3 := Eq.trans h1.symm ( W_is_Female isWitness a1 a2 a5 )
  --   show father=mother ∨ father=daughter from absurd h3 h2


lemma FA_or_SA : accessory=father ∨ accessory=son  := by
  cases accessory with
  | father => apply Or.inl; rfl
  | son => apply Or.inr; rfl
  | _ => 
    apply False.elim
    . cases (MW_or_DW isWitness a1 a2 a5) with
      | _ h => apply (h ▸ a1); exact Eq.refl (sex _)

-- youngest_is_daughter {role} [preorder] {youngest} {oldest} (isYoungest) (isOldest) {murderer}{victim}{witness}{accessory} (isMurderer) (isVictim) (isWitness) (isAccessory) (a1) (a2) (a3) (a4) (a5) (a6)
theorem youngest_is_daughter: youngest = daughter  := by
  cases youngest with
  | daughter => rfl
  | father => 
    apply False.elim
    . have h1 : father ≤ daughter := le_of_lt (isYoungest daughter noConfusion)
      have h2 : ¬ (father ≤ daughter) := not_le_of_gt ((a5 ▸ isOldest) daughter noConfusion)
      exact h2 h1
  | mother => 
    apply False.elim
    . have h1 : mother ≤ daughter := le_of_lt (isYoungest daughter noConfusion)
      have h2 : ¬ (mother ≤ daughter) := not_le_of_gt (mother_older_then_children.left)
      exact h2 h1
  | son => 
    cases victim with
    | father => exact False.elim (a3 rfl)
    | son => exact False.elim (a3 rfl)
    | mother => 
      have h0: role mother=Victim := isVictim
      have h1: role mother ≠ Witness := h0 ▸ noConfusion
      have h2: Witness = role witness := isWitness.symm
      have h3: role mother ≠ role witness  := h2 ▸ h1
      have h4:  mother ≠ witness  := mt (congrArg role) h3

      have h5:  witness=daughter  := match (MW_or_DW isWitness a1 a2 a5) with
        | .inr h => h
        | .inl h => False.elim ((Ne.symm h4) h) 

      have h6 : murderer ≠ son := a6
      have h7 : murderer=father ∨ murderer=son := by
        cases murderer with
        | father => apply Or.inl; rfl
        | mother => exact Roles.noConfusion (h0 ▸ isMurderer)
        | son => apply Or.inr; rfl
        | daughter =>  exact Roles.noConfusion (isWitness ▸ h5.symm ▸ isMurderer)
      have h8 : murderer=father := mtp h7.symm h6

      have h9 : accessory=son := by
        cases accessory with
        | father => exact Roles.noConfusion (isMurderer ▸ h8.symm ▸ isAccessory)
        | mother => exact Roles.noConfusion (h0 ▸ isAccessory)
        | son => rfl
        | daughter =>  exact Roles.noConfusion (isWitness ▸ h5.symm ▸ isAccessory)

      ------------------------
      exact absurd mother_older_then_children.right (lt_asymm (h9 ▸  a4)) 
    | daughter => 
      have h0: role daughter=Victim := isVictim
      have h1: role daughter ≠ Witness := h0 ▸ noConfusion
      have h2: Witness = role witness := isWitness.symm
      have h3: role daughter ≠ role witness  := h2 ▸ h1
      have h4:  daughter ≠ witness  := mt (congrArg role) h3

      have h5:  witness=mother  := match (MW_or_DW isWitness a1 a2 a5) with
        | .inl h => h
        | .inr h => False.elim ((Ne.symm h4) h) 

      -- have h6 : murderer ≠ son := a6
      have h7 : murderer=father ∨ murderer=son := by
        cases murderer with
        | father => apply Or.inl; rfl
        | daughter => exact Roles.noConfusion (h0 ▸ isMurderer)
        | son => exact False.elim (a6 rfl)
        | mother =>  exact Roles.noConfusion (isWitness ▸ h5.symm ▸ isMurderer)
      have h8 : murderer=father := mtp h7.symm a6

      have h9 : accessory=son := by
        cases accessory with
        | father => exact Roles.noConfusion (isMurderer ▸ h8.symm ▸ isAccessory)
        | daughter => exact Roles.noConfusion (h0 ▸ isAccessory)
        | son => rfl
        | mother =>  exact Roles.noConfusion (isWitness ▸ h5.symm ▸ isAccessory)

      ------------------------
      have h10 : ¬son < daughter:= lt_asymm (h9 ▸ a4)
      have h11 : son < daughter := (isYoungest daughter) noConfusion
      exact absurd h11 h10


theorem solution : witness = daughter ∧ victim = son ∧ accessory = father ∧ murderer = mother  := by
    have yyy : youngest = daughter := youngest_is_daughter isYoungest isOldest isMurderer isVictim isWitness isAccessory a1 a2 a3 a4 a5 a6

    cases victim with
    | daughter => exact False.elim (a3 (yyy ▸ rfl))
    | mother => exact False.elim (a3 (yyy ▸ rfl))  
    | father => 
      have h0: role father=Victim := isVictim
      have h1: role father ≠ Accessory := h0 ▸ noConfusion
      have h2: Accessory = role accessory := isAccessory.symm
      have h3: role father ≠ role accessory  := h2 ▸ h1
      have h4:  father ≠ accessory  := mt (congrArg role) h3

      have h5:  accessory=son  := match (FA_or_SA isWitness isAccessory a1 a2 a4 a5) with
        | .inr h => h
        | .inl h => False.elim ((Ne.symm h4) h) 

      -- have h6 : murderer ≠ daughter := yyy ▸ a6
      -- -- have h6 : witness ≠ mother := sorry
      -- have h7 : murderer=daughter ∨ murderer=mother := by
      --   cases murderer with
      --   | daughter => apply Or.inl; rfl
      --   | father => exact Roles.noConfusion (h0 ▸ isMurderer)
      --   | mother => apply Or.inr; rfl
      --   | son =>  exact Roles.noConfusion (isAccessory ▸ h5.symm ▸ isMurderer)
      -- have h8 : murderer=mother := mtp h7 h6

      -- have h9 : witness=daughter := by
      --   cases witness with
      --   | daughter => rfl
      --   | father => exact Roles.noConfusion (h0 ▸ isWitness)
      --   | mother => exact Roles.noConfusion (isMurderer ▸ h8.symm ▸ isWitness)
      --   | son =>  exact Roles.noConfusion (isAccessory ▸ h5.symm ▸ isWitness)

      ------------------------

      have hnlt : ¬(son < father):= lt_asymm (h5 ▸  a4)
      have hlt : (father > son) := (a5 ▸ (isOldest son)) noConfusion
      exact absurd hlt hnlt

    | son => 
      have h0: role son=Victim := isVictim
      have h1: role son ≠ Accessory := h0 ▸ noConfusion
      have h2: Accessory = role accessory := isAccessory.symm
      have h3: role son ≠ role accessory  := h2 ▸ h1
      have h4:  son ≠ accessory  := mt (congrArg role) h3

      have h5:  accessory=father  := match (FA_or_SA isWitness isAccessory a1 a2 a4 a5) with
        | .inl h => h
        | .inr h => False.elim ((Ne.symm h4) h) 

      have h6 : murderer ≠ daughter := yyy ▸ a6
      -- have h6 : witness ≠ mother := sorry
      have h7 : murderer=daughter ∨ murderer=mother := by
        cases murderer with
        | daughter => apply Or.inl; rfl
        | son => exact Roles.noConfusion (h0 ▸ isMurderer)
        | mother => apply Or.inr; rfl
        | father =>  exact Roles.noConfusion (isAccessory ▸ h5.symm ▸ isMurderer)
      have h8 : murderer=mother := mtp h7 h6

      have h9 : witness=daughter := by
        cases witness with
        | daughter => rfl
        | son => exact Roles.noConfusion (h0 ▸ isWitness)
        | mother => exact Roles.noConfusion (isMurderer ▸ h8.symm ▸ isWitness)
        | father =>  exact Roles.noConfusion (isAccessory ▸ h5.symm ▸ isWitness)

      exact ⟨h9, rfl, h5, h8⟩


def hello := s!"world. You are using Lean version {Lean.versionString} "
#eval hello
#eval "PROOVED!!!"
