import Mathlib.Init.Algebra.Order
import Supertype
namespace Subtype
variable (s : Subtype p)

def proof := s.property

end Subtype
/-  disjunctive syllogism -/
theorem mtp {p q : Prop} (hpq: p ∨ q)(hnp: ¬ p):  q :=  by cases hpq ; contradiction ; assumption

----------------------
inductive FamilyMembers where | father | mother | son | daughter open FamilyMembers
inductive Roles where | murderer | victim | witness | accessory open Roles

inductive Sexes where | male | female open Sexes

-- variable
--   { whois: Roles → FamilyMembers }
--   { oneToOne: ∀ r1 r2, r1 ≠ r2 → whois r1 ≠ whois r2 }
abbrev injection := {f : Roles → FamilyMembers // ∀ r1 r2, f r1 = f r2 → r1 = r2}
variable { whois: injection }

def sex: FamilyMembers → Sexes
  | father => male
  | mother => female
  | son => male
  | daughter => female

-----------------

-- variable [LE FamilyMembers] [LT FamilyMembers]
variable [po:Preorder FamilyMembers]

variable { youngest : {m: FamilyMembers \\ ∀ x, x ≠ m → m < x} }
variable { oldest : {m: FamilyMembers \\ ∀ x, x ≠ m → m > x} }

axiom mother_older_then_children: mother > daughter ∧ mother > son

----------------------------------  

variable ( a1: (sex (whois.val accessory)) ≠ (sex (whois.val witness)) ) #check @a1
variable ( a2: (sex oldest) ≠ (sex (whois.val witness)) ) #check @a2
variable ( a3: (sex youngest) ≠ (sex (whois.val victim)) ) #check @a3
variable ( a4: (whois.val accessory) > (whois.val victim) )  #check @a4
variable ( a5: oldest = father ) #check @a5
variable ( a6: (whois.val murderer) ≠ youngest ) #check @a6


-------------------------------
lemma W_is_Female: (sex (whois.val witness)) = female := by
  have h1: (sex father) ≠ (sex (whois.val witness)) := a5 ▸ a2
  have h2: (sex father) = male := rfl
  have h3: (sex (whois.val witness)) ≠ male := Ne.symm (h2 ▸ h1)
  
  cases h:(whois.val witness)
  . exact False.elim ((h ▸ h3) rfl) -- father
  . rfl -- mother
  . exact False.elim ((h ▸ h3) rfl) -- son
  . rfl -- daughter

lemma A_is_Male: (sex (whois.val accessory)) = male := by
  have h: (sex (whois.val accessory)) ≠ female:= ( W_is_Female a2 a5 ) ▸ a1

  cases hh:(whois.val accessory)
  . rfl
  . apply False.elim ; rw [hh, sex] at h ; contradiction
  . rfl
  . apply False.elim ; rw [hh, sex] at h ; contradiction

lemma MW_or_DW : (whois.val witness)=mother ∨ (whois.val witness)=daughter :=   by
  have h4: (sex (whois.val witness)) = female := W_is_Female a2 a5

  cases h:(whois.val witness)
  · apply False.elim ; simp [h, sex] at h4
  · apply Or.inl ; rfl
  · apply False.elim ; simp [h, sex] at h4
  · apply Or.inr ; rfl

  -- have h1: (sex father) ≠ (sex (whois.val witness)) := a5 ▸ a2
  -- have h2: (sex father) = male := rfl
  -- have h3: (sex (whois.val witness)) ≠ male := Ne.symm (h2 ▸ h1)
  -- have h4: (sex (whois.val witness)) = female := eq_female_of_ne_male (sex (whois.val witness)) h3

  -- match (whois.val witness) with
  -- | mother => 
  --   have h : mother = mother := rfl
  --   show mother=mother ∨ mother=daughter from Or.inl h
  -- | daughter =>
  --   have h : daughter = daughter := rfl
  --   show daughter=mother ∨ daughter=daughter from Or.inr h
  -- | son => 
  --   have h1 : sex son = male := rfl
  --   have h2 : male ≠ female := Sexes.noConfusion -- or by simp
  --   have h3 := Eq.trans h1.symm ( W_is_Female a2 a5 )  
  --   show son=mother ∨ son=daughter from absurd h3 h2
  -- | father => 
  --   have h1 : sex father = male := rfl
  --   have h2 : male ≠ female := Sexes.noConfusion -- or by simp
  --   have h3 := Eq.trans h1.symm ( W_is_Female a2 a5 )
  --   show father=mother ∨ father=daughter from absurd h3 h2

lemma FA_or_SA : (whois.val accessory)=father ∨ (whois.val accessory)=son  := by
  cases hw:(whois.val accessory) with
  | father => apply Or.inl; rfl
  | son => apply Or.inr; rfl
  | _ => 
    apply False.elim
    . cases (MW_or_DW a2 a5) with
      | _ h => apply (hw ▸ h ▸ a1); exact Eq.refl (sex _)

lemma whois_trans {m: FamilyMembers} {r1 r2: Roles} (h1: whois.val r1 = m) (h2: whois.val r2 = m): r1 = r2 := (whois.proof r1 r2) (Eq.trans h1 h2.symm)

-- youngest_is_daughter {role} [preorder] {youngest} {oldest} (isYoungest) (isOldest) {murderer}{victim}{witness}{accessory} (isMurderer) (isVictim) (isWitness) (isAccessory) (a1) (a2) (a3) (a4) (a5) (a6)
  -- cases youngest with | mk st hpf  => cases st with | mk yval => cases yval with
theorem youngest_is_daughter: youngest = daughter  := by
  let ⟨⟨yval,_⟩,hpf,_,_⟩  := youngest
  cases yval with
  | daughter => rfl
  | father => 
    apply False.elim
    . have h1 : father ≤ daughter := le_of_lt (hpf daughter noConfusion)
      have h2 : ¬ (father ≤ daughter) := not_le_of_gt ((a5 ▸ oldest.proof) daughter noConfusion)
      exact h2 h1
  | mother => 
    apply False.elim
    . have h1 : mother ≤ daughter := le_of_lt (hpf daughter noConfusion)
      have h2 : ¬ (mother ≤ daughter) := not_le_of_gt (mother_older_then_children.left)
      exact h2 h1
  | son => 
    cases h0':(whois.val victim) with
    | father => simp_all; exact False.elim (a3 rfl)
    | son => simp_all -- ; exact False.elim (a3 rfl)
    | mother => 
      have h2: victim ≠ witness := Roles.noConfusion
      have h3: whois.val victim = whois.val witness → victim = witness := whois.proof victim witness
      have h4: mother ≠ (whois.val witness)  := h0' ▸ (mt h3 h2)

      have h5:  (whois.val witness)=daughter  := match (MW_or_DW  a2 a5) with
        | .inr h => h
        | .inl h => False.elim ((Ne.symm h4) h) 

      have h6 : (whois.val murderer) ≠ son := a6
      have h7 : (whois.val murderer)=father ∨ (whois.val murderer)=son := by
        cases h7':(whois.val murderer) with
        | father => apply Or.inl; rfl
        | mother => exact Roles.noConfusion (whois_trans h0' h7')
        | son => apply Or.inr; rfl
        | daughter =>  exact Roles.noConfusion (whois_trans h5 h7')
      have h8 : (whois.val murderer)=father := mtp h7.symm h6

      have h9 : (whois.val accessory)=son := by
        cases h9':(whois.val accessory) with
        | father => exact Roles.noConfusion (whois_trans h9' h8)
        | mother => exact Roles.noConfusion (whois_trans h9' h0')
        | son => rfl
        | daughter =>  exact Roles.noConfusion (whois_trans h9' h5)

      ------------------------
      exact absurd mother_older_then_children.right (lt_asymm (h9 ▸  h0' ▸ a4)) 
    | daughter => 
      have h2: victim ≠ witness := Roles.noConfusion
      have h3: whois.val victim = whois.val witness → victim = witness := whois.proof victim witness
      have h4:  daughter ≠ (whois.val witness)  := h0' ▸ (mt h3 h2)

      have h5:  (whois.val witness)=mother  := match (MW_or_DW  a2 a5) with
        | .inl h => h
        | .inr h => False.elim ((Ne.symm h4) h) 

      -- have h6 : (whois.val murderer) ≠ son := a6
      have h7 : (whois.val murderer)=father ∨ (whois.val murderer)=son := by
        cases h7':(whois.val murderer) with
        | father => apply Or.inl; rfl
        | daughter => exact Roles.noConfusion (whois_trans h7' h0')
        | son => exact False.elim ((h7' ▸ a6) rfl)
        | mother =>  exact Roles.noConfusion (whois_trans h7' h5)
      have h8 : (whois.val murderer)=father := mtp h7.symm a6

      have h9 : (whois.val accessory)=son := by
        cases h9':(whois.val accessory) with
        | father => exact Roles.noConfusion (whois_trans h9' h8)
        | daughter => exact Roles.noConfusion (whois_trans h9' h0')
        | son => rfl
        | mother =>  exact Roles.noConfusion (whois_trans h9' h5)

      ------------------------
      have h10 : ¬son < daughter:= lt_asymm (h9 ▸ h0' ▸ a4)
      have h11 : son < daughter := (hpf daughter) noConfusion
      exact absurd h11 h10


theorem solution : (whois.val witness) = daughter ∧ (whois.val victim) = son ∧ (whois.val accessory) = father ∧ (whois.val murderer) = mother  := by
    have yyy : youngest = daughter := youngest_is_daughter  a2 a3 a4 a5 a6

    cases h0':(whois.val victim) with
    | daughter => exact False.elim (a3 (yyy ▸ h0' ▸ rfl))
    | mother => exact False.elim (a3 (yyy ▸ h0' ▸ rfl))  
    | father => 
      have h2: victim ≠ accessory := Roles.noConfusion
      have h3: whois.val victim = whois.val accessory → victim = accessory := whois.proof victim accessory
      have h4:  father ≠ (whois.val accessory)  := h0' ▸ (mt h3 h2)

      have h5:  (whois.val accessory)=son  := match (FA_or_SA  a1 a2 a5) with
        | .inr h => h
        | .inl h => False.elim ((Ne.symm h4) h) 

      -- have h6 : (whois.val murderer) ≠ daughter := yyy ▸ a6
      -- -- have h6 : (whois.val witness) ≠ mother := sorry
      -- have h7 : (whois.val murderer)=daughter ∨ (whois.val murderer)=mother := by
      --   cases (whois.val murderer) with
      --   | daughter => apply Or.inl; rfl
      --   | father => exact Roles.noConfusion (h0 ▸ isMurderer)
      --   | mother => apply Or.inr; rfl
      --   | son =>  exact Roles.noConfusion (isAccessory ▸ h5.symm ▸ isMurderer)
      -- have h8 : (whois.val murderer)=mother := mtp h7 h6

      -- have h9 : (whois.val witness)=daughter := by
      --   cases (whois.val witness) with
      --   | daughter => rfl
      --   | father => exact Roles.noConfusion (h0 ▸ isWitness)
      --   | mother => exact Roles.noConfusion (isMurderer ▸ h8.symm ▸ isWitness)
      --   | son =>  exact Roles.noConfusion (isAccessory ▸ h5.symm ▸ isWitness)

      ------------------------

      have hnlt : ¬(son < father):= lt_asymm (h5 ▸ h0' ▸ a4)
      have hlt : (father > son) := (a5 ▸ (oldest.proof son)) noConfusion
      exact absurd hlt hnlt

    | son => 
      have h2: victim ≠ accessory := Roles.noConfusion
      have h3: whois.val victim = whois.val accessory → victim = accessory := whois.proof victim accessory

      have h4:  son ≠ (whois.val accessory)  := h0' ▸ (mt h3 h2)

      have h5:  (whois.val accessory)=father  := match (FA_or_SA a1 a2 a5) with
        | .inl h => h
        | .inr h => False.elim ((Ne.symm h4) h) 

      have h6 : (whois.val murderer) ≠ daughter := yyy ▸ a6
      -- have h6 : (whois.val witness) ≠ mother := sorry
      have h7 : (whois.val murderer)=daughter ∨ (whois.val murderer)=mother := by
        cases h7':(whois.val murderer) with
        | daughter => apply Or.inl; rfl
        | son => exact Roles.noConfusion (whois_trans h7' h0')
        | mother => apply Or.inr; rfl
        | father =>  exact Roles.noConfusion (whois_trans h7' h5)
      have h8 : (whois.val murderer)=mother := mtp h7 h6

      have h9 : (whois.val witness)=daughter := by
        cases h9':(whois.val witness) with
        | daughter => rfl
        | son => exact Roles.noConfusion (whois_trans h9' h0')
        | mother => exact Roles.noConfusion (whois_trans h9' h8)
        | father =>  exact Roles.noConfusion (whois_trans h9' h5)

      exact ⟨h9, rfl, h5, h8⟩

def whois_val' := fun 
                | victim => son 
                | accessory => father
                | murderer => mother 
                | witness => daughter

theorem whoisOneToOne : ∀ r1 r2, whois_val' r1 = whois_val' r2 → r1 = r2 := fun r1 r2 h =>
  by cases r1 with
  | _ => cases r2 with
    | _ => simp [whois_val'] at *

def whois': injection := ⟨whois_val',  whoisOneToOne⟩

theorem solution' : whois = whois' := 
  have ⟨ hwd, hvs, haf, hmm ⟩ := solution a1 a2 a3 a4 a5 a6
  suffices h0 : (whois.val = whois'.val) from Subtype.eq h0
  suffices h : (∀ r, whois.val r = whois'.val r) from funext h
  fun
    | witness => Eq.trans hwd rfl
    | victim => Eq.trans hvs rfl
    | accessory => Eq.trans haf rfl
    | murderer => Eq.trans hmm rfl

