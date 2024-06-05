/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/


import Smt.Util.Mathlib.Init



namespace Smt



/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  protected
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt a b :=
    a ≤ b ∧ ¬ b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
    by intros ; rfl

section top_level
variable [Preorder α]

@[simp]
theorem le_refl : ∀ a : α, a ≤ a :=
  Preorder.le_refl

theorem le_rfl {a : α} : a ≤ a :=
  le_refl a

theorem le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
  Preorder.le_trans _ _ _

theorem lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Preorder.lt_iff_le_not_le _ _

theorem le_of_lt : ∀ {a b : α}, a < b → a ≤ b :=
  fun h => lt_iff_le_not_le.mp h |>.1

theorem lt_of_le_not_le : ∀ {a b : α}, a ≤ b → ¬b ≤ a → a < b
| _a, _b, hab, hba => lt_iff_le_not_le.mpr ⟨hab, hba⟩

theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | _a, _b, hab => lt_iff_le_not_le.mp hab

theorem not_le_of_lt {a b : α} (h : a < b) : ¬b ≤ a :=
  (le_not_le_of_lt h).right

abbrev LT.not_le := @not_le_of_lt

theorem lt_trans : ∀ {a b c : α}, a < b → b < c → a < c
| a, b, c => by
  simp [Preorder.lt_iff_le_not_le]
  intro aLEb _n_bLEa bLEc n_cLEb
  exact ⟨le_trans aLEb bLEc, fun cLEa => le_trans cLEa aLEb |> n_cLEb⟩

theorem ge_trans : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c :=
  fun h₁ h₂ => le_trans h₂ h₁

theorem gt_trans : ∀ {a b c : α}, a > b → b > c → a > c :=
  fun h₁ h₂ => lt_trans h₂ h₁



theorem lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c
| _a, _b, _c, hab, hbc =>
  let ⟨hab, hba⟩ := le_not_le_of_lt hab
  lt_of_le_not_le (le_trans hab hbc) fun hca => hba (le_trans hbc hca)

theorem lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c
  | _a, _b, _c, hab, hbc =>
    let ⟨hbc, hcb⟩ := le_not_le_of_lt hbc
    lt_of_le_not_le (le_trans hab hbc) fun hca => hcb (le_trans hca hab)

theorem gt_of_gt_of_ge {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
  lt_of_le_of_lt h₂ h₁

theorem gt_of_ge_of_gt {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
  lt_of_lt_of_le h₂ h₁

theorem not_le_of_gt {a b : α} (h : a > b) : ¬a ≤ b :=
  le_not_le_of_lt h |>.right

theorem not_lt_of_ge {a b : α} (h : a ≥ b) : ¬ a < b := fun hab =>
  not_le_of_gt hab h

instance (priority := 900) : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
instance (priority := 900) : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
instance (priority := 900) : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
instance (priority := 900) : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
instance (priority := 900) : @Trans α α α GT.gt GE.ge GT.gt := ⟨gt_of_gt_of_ge⟩
instance (priority := 900) : @Trans α α α GE.ge GT.gt GT.gt := ⟨gt_of_ge_of_gt⟩
end top_level




namespace Preorder
variable [Preorder α]

def decidableLTOfDecidableLE [@DecidableRel α (· ≤ ·)] : @DecidableRel α (· < ·)
| a, b =>
  if hab : a ≤ b then
    if hba : b ≤ a
    then isFalse fun hab' => not_le_of_gt hab' hba
    else isTrue <| lt_of_le_not_le hab hba
  else isFalse fun hab' => hab (le_of_lt hab')
end Preorder



/-- A partial order is a reflexive, transitive, antisymmetric relation `≤`. -/
class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b

section top_level
variable [PartialOrder α]

theorem le_antisymm {a b : α} : a ≤ b → b ≤ a → a = b :=
  PartialOrder.le_antisymm a b

theorem lt_of_le_ne {a b : α} : a ≤ b → a ≠ b → a < b := by
  intro h_ab h_eq
  rw [lt_iff_le_not_le]
  apply And.intro h_ab
  intro h_ba
  let wrong := le_antisymm h_ab h_ba
  contradiction
end top_level



/-- A linear order is reflexive, transitive, antisymmetric and total relation `≤`.

We assume that every linear ordered type has decidable `≤`, `<`, and `=`.
-/
class LinearOrder (α : Type u) extends PartialOrder α, Min α, Max α, Ord α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a
  decidableLE : @DecidableRel α (· ≤ ·)
  -- decidableEq : DecidableEq α := by
  decidableLT : @DecidableRel α (· < ·)

section top_level
instance Nat.instLinearOrder : LinearOrder Nat where
  le_refl := Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := Nat.le_total
  decidableLE := inferInstance
  decidableLT := inferInstance
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le

instance Int.instLinearOrder : LinearOrder Int where
  le_refl := Int.le_refl
  le_trans := @Int.le_trans
  le_antisymm := @Int.le_antisymm
  le_total := Int.le_total
  decidableLE := inferInstance
  decidableLT := inferInstance
  lt_iff_le_not_le := @Int.lt_iff_le_not_le

variable [inst : LinearOrder α]

scoped instance : @DecidableRel α (· ≤ ·) :=
  inst.decidableLE
scoped instance : @DecidableRel α (· < ·) :=
  inst.decidableLT

theorem le_total : ∀ (a b : α), a ≤ b ∨ b ≤ a :=
  LinearOrder.le_total

theorem lt_or_eq_of_le
  {a b : α} (hab : a ≤ b)
: a < b ∨ a = b :=
  if hba : b ≤ a
  then Or.inr (le_antisymm hab hba)
  else Or.inl (lt_of_le_not_le hab hba)

theorem lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a :=
  le_total a b |>.elim
    (fun h : a ≤ b =>
      lt_or_eq_of_le h |>.elim
        (fun h : a < b => Or.inl h)
        fun h : a = b => Or.inr (Or.inl h))
    fun h : b ≤ a =>
      lt_or_eq_of_le h |>.elim
        (fun h : b < a => Or.inr (Or.inr h))
        fun h : b = a => Or.inr (Or.inl h.symm)

theorem le_of_not_lt {a b : α} (h : ¬b < a) : a ≤ b :=
  match lt_trichotomy a b with
  | Or.inl hlt => le_of_lt hlt
  | Or.inr (Or.inl HEq) => HEq ▸ le_refl a
  | Or.inr (Or.inr hgt) => absurd hgt h

theorem le_of_not_gt {a b : α} : ¬a > b → a ≤ b :=
  le_of_not_lt

theorem lt_of_not_ge {a b : α} (h : ¬a ≥ b) : a < b :=
  lt_of_le_not_le ((le_total _ _).resolve_right h) h

theorem lt_iff_not_ge (x y : α) : x < y ↔ ¬x ≥ y :=
  ⟨not_le_of_gt, lt_of_not_ge⟩

@[simp]
theorem not_lt {a b : α} : ¬a < b ↔ b ≤ a :=
  ⟨le_of_not_gt, not_lt_of_ge⟩

@[simp]
theorem not_le {a b : α} : ¬a ≤ b ↔ b < a :=
  (lt_iff_not_ge _ _).symm
end top_level



def GaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) :=
  ∀ a b, l a ≤ b ↔ a ≤ u b
