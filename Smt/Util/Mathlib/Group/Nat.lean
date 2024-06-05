/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/



import Smt.Util.Mathlib.Group.Basic

namespace Smt.Nat

variable [AddMonoidWithOne α]

@[simp, norm_cast]
theorem cast_zero : ((0 : Nat) : α) = 0 :=
  AddMonoidWithOne.natCast_zero

-- Lemmas about `Nat.succ` need to get a low priority, so that they are tried last.
-- This is because `Nat.succ _` matches `1`, `3`, `x+1`, etc.
-- Rewriting would then produce really wrong terms.
@[norm_cast 500]
theorem cast_succ (n : Nat) : ((n.succ : Nat) : α) = n + 1 :=
  AddMonoidWithOne.natCast_succ _

theorem cast_add_one (n : Nat) : ((n + 1 : Nat) : α) = n + 1 :=
  cast_succ _

@[simp, norm_cast]
theorem cast_ite (P : Prop) [Decidable P] (m n : Nat) :
    ((ite P m n : Nat) : α) = ite P (m : α) (n : α) := by
  split <;> rfl

@[simp, norm_cast]
theorem cast_one [AddMonoidWithOne α] : ((1 : Nat) : α) = 1 := by
  rw [cast_succ, Nat.cast_zero, zero_add]

@[simp, norm_cast]
theorem cast_add [AddMonoidWithOne α] (m n : Nat) : ((m + n : Nat) : α) = m + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_succ, cast_succ, ih, cast_succ, add_assoc]

/-- Computationally friendlier cast than `Nat.unaryCast`, using binary representation. -/
protected def binCast [Zero α] [One α] [Add α] : Nat → α
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0
    then (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2))
    else (Nat.binCast ((n + 1) / 2)) + (Nat.binCast ((n + 1) / 2)) + 1
