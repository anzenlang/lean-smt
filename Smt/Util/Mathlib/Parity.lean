/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/



namespace Smt



namespace Nat

def Even (n : Nat) : Prop :=
  ∃ r, n = r + r

def Odd (n : Nat) : Prop :=
  ∃ r, n = 2 * r + 1



section basics

@[simp]
theorem even_add_self (a : Nat) : Even (a + a) :=
  ⟨a, rfl⟩

theorem even_iff : Even n ↔ n % 2 = 0 :=
  ⟨ fun ⟨m, hm⟩ => by simp [← Nat.mul_two, hm],
    fun h => ⟨n / 2, by omega⟩ ⟩

instance : DecidablePred Even :=
  fun _ => decidable_of_iff _ even_iff.symm

theorem odd_iff : Odd n ↔ n % 2 = 1 :=
  ⟨ fun ⟨m, hm⟩ => by omega,
    fun h => ⟨n / 2, by omega⟩ ⟩

instance : DecidablePred Odd :=
  fun _ => decidable_of_iff _ odd_iff.symm



@[simp]
theorem even_zero : Even 0 := by decide
@[simp]
theorem not_even_one : ¬ Even 1 := by decide
@[simp]
theorem even_two : Even 2 := by decide

@[simp]
theorem not_odd_zero : ¬ Odd 0 := by decide
@[simp]
theorem odd_one : Odd 1 := by decide
@[simp]
theorem not_odd_two : ¬ Odd 2 := by decide



@[simp]
theorem mod_two_ne_zero : ¬ n % 2 = 0 ↔ n % 2 = 1 := by
  omega

@[simp]
theorem mod_two_ne_one : ¬ n % 2 = 1 ↔ n % 2 = 0 := by
  omega

theorem even_add : Even (m + n) ↔ (Even m ↔ Even n) := by
  cases Nat.mod_two_eq_zero_or_one m
  <;> cases Nat.mod_two_eq_zero_or_one n
  <;> simp only [even_iff]
  <;> omega

theorem even_add_one : Even (n + 1) ↔ ¬ Even n :=
  by simp [even_add]

end basics



section even_odd_iff

theorem not_even_iff : ¬ Even n ↔ n % 2 = 1 := by
  rw [even_iff, mod_two_ne_zero]

theorem not_odd_iff : ¬ Odd n ↔ n % 2 = 0 := by
  rw [odd_iff, mod_two_ne_one]

theorem even_iff_not_odd : Even n ↔ ¬ Odd n := by
  rw [not_odd_iff, even_iff]

@[simp]
theorem odd_iff_not_even : Odd n ↔ ¬ Even n := by
  rw [not_even_iff, odd_iff]

end even_odd_iff
