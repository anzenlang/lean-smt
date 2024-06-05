/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

import Smt.Util.Mathlib.Init



namespace Smt



section basics
variable (M : Type u) (N : Type v) (μ : M → N → N) (r : N → N → Prop)

def Covariant : Prop :=
  ∀ (m : M) {n₁ n₂ : N}, r n₁ n₂ → r (μ m n₁) (μ m n₂)

def Contravariant : Prop :=
  ∀ (m : M) {n₁ n₂ : N}, r (μ m n₁) (μ m n₂) → r n₁ n₂

class CovariantClass : Prop where
  protected elim : Covariant M N μ r

class ContravariantClass : Prop where
  protected elim : Contravariant M N μ r

theorem rel_iff_cov
  [CovariantClass M N μ r]
  [ContravariantClass M N μ r]
  (m : M) {a b : N}
: r (μ m a) (μ m b) ↔ r a b :=
  ⟨ContravariantClass.elim _, CovariantClass.elim _⟩
end basics



section instances

instance instCovariantNatAddLT : CovariantClass Nat Nat (· + ·) (· < ·) where
  elim := by
    simp only [Covariant]
    omega
instance instCovariantNatSwapAddLT : CovariantClass Nat Nat (swap (· + ·)) (· < ·) where
  elim := by
    simp only [Covariant, swap]
    omega
instance instCovariantNatAddLE : CovariantClass Nat Nat (· + ·) (· ≤ ·) where
  elim := by
    simp only [Covariant]
    omega
instance instCovariantNatSwapAddLE : CovariantClass Nat Nat (swap (· + ·)) (· ≤ ·) where
  elim := by
    simp only [Covariant, swap]
    omega



-- -- should not need this, these instances are obtained by `LinearOrderedRing Int`
-- instance instCovariantIntAddLT : CovariantClass Int Int (· + ·) (· < ·) where
--   elim := by
--     simp only [Covariant]
--     omega
-- instance instCovariantIntSwapAddLT : CovariantClass Int Int (swap (· + ·)) (· < ·) where
--   elim := by
--     simp only [Covariant, swap]
--     omega
-- instance instCovariantIntAddLE : CovariantClass Int Int (· + ·) (· ≤ ·) where
--   elim := by
--     simp only [Covariant]
--     omega
-- instance instCovariantIntSwapAddLE : CovariantClass Int Int (swap (· + ·)) (· ≤ ·) where
--   elim := by
--     simp only [Covariant, swap]
--     omega

end instances



section
variable [LE α] [LT α]

theorem add_le_add_left
  [Add α] [CovariantClass α α (· + ·) (· ≤ ·)]
  {b c : α} (hbc : b ≤ c) (a : α)
: a + b ≤ a + c :=
  CovariantClass.elim _ hbc

theorem add_le_add_right
  [Add α] [inst : CovariantClass α α (swap (· + ·)) (· ≤ ·)]
  {b c : α} (hbc : b ≤ c) (a : α)
: b + a ≤ c + a :=
  inst.elim _ hbc

theorem add_lt_add_left
  [Add α] [CovariantClass α α (· + ·) (· < ·)]
  {b c : α} (hbc : b < c) (a : α)
: a + b < a + c :=
  CovariantClass.elim _ hbc

theorem add_lt_add_right
  [Add α] [inst : CovariantClass α α (swap (· + ·)) (· < ·)]
  {b c : α} (hbc : b < c) (a : α)
: b + a < c + a :=
  inst.elim _ hbc

theorem mul_lt_mul_iff_left
  [Mul α] [CovariantClass α α (· * ·) (· < ·)] [ContravariantClass α α (· * ·) (· < ·)]
  (a : α) {b c : α}
: a * b < a * c ↔ b < c :=
  rel_iff_cov α α (· * ·) (· < ·) a

theorem mul_lt_mul_iff_right
  [Mul α] [CovariantClass α α (swap (· * ·)) (· < ·)]
  [ContravariantClass α α (swap (· * ·)) (· < ·)]
  (a : α) {b c : α}
: b * a < c * a ↔ b < c :=
  rel_iff_cov α α (swap (· * ·)) (· < ·) a

theorem add_lt_add_iff_left
  [Add α] [CovariantClass α α (· + ·) (· < ·)] [ContravariantClass α α (· + ·) (· < ·)]
  (a : α) {b c : α}
: a + b < a + c ↔ b < c :=
  rel_iff_cov α α (· + ·) (· < ·) a

theorem add_lt_add_iff_right
  [Add α]
  [CovariantClass α α (swap (· + ·)) (· < ·)]
  [ContravariantClass α α (swap (· + ·)) (· < ·)]
  (a : α) {b c : α}
: b + a < c + a ↔ b < c :=
  rel_iff_cov α α (swap (· + ·)) (· < ·) a

theorem add_le_add_iff_left
  [Add α]
  [CovariantClass α α (· + ·) (· ≤ ·)]
  [ContravariantClass α α (· + ·) (· ≤ ·)]
  (a : α) {b c : α}
: a + b ≤ a + c ↔ b ≤ c :=
  rel_iff_cov α α (· + ·) (· ≤ ·) a

theorem add_le_add_iff_right
  [Add α] [LE α]
  [CovariantClass α α (swap (· + ·)) (· ≤ ·)] [ContravariantClass α α (swap (· + ·)) (· ≤ ·)]
  (a : α) {b c : α}
: b + a ≤ c + a ↔ b ≤ c :=
  rel_iff_cov α α (swap (· + ·)) (· ≤ ·) a
end
