/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/



import Smt.Util.Mathlib.Group.Basic



namespace Smt.Int



instance instCommMonoid : CommMonoid Int where
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  mul_assoc := Int.mul_assoc



instance instAddCommGroup : AddCommGroup Int where
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : Int) * x = n * x + x
    by rw [Int.add_mul, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [Int.ofNat_eq_coe, Int.ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by simp only [Int.negSucc_coe, Int.ofNat_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

instance instAddCommMonoid : AddCommMonoid Int :=
  by infer_instance
instance instAddMonoid : AddMonoid Int :=
  by infer_instance
instance instMonoid : Monoid Int :=
  by infer_instance
instance instCommSemigroup : CommSemigroup Int :=
  by infer_instance
instance instSemigroup : Semigroup Int :=
  by infer_instance
instance instAddGroup : AddGroup Int :=
  by infer_instance
instance instAddCommSemigroup : AddCommSemigroup Int :=
  by infer_instance
instance instAddSemigroup : AddSemigroup Int :=
  by infer_instance

instance instCommRing : CommRing Int where
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  mul_comm := Int.mul_comm
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ n x := rfl
  mul_assoc := Int.mul_assoc
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_left_neg := Int.add_left_neg
  nsmul := (·*·)
  nsmul_zero := Int.zero_mul
  nsmul_succ n x :=
    show (n + 1 : Int) * x = n * x + x
    by rw [Int.add_mul, Int.one_mul]
  zsmul := (·*·)
  zsmul_zero' := Int.zero_mul
  zsmul_succ' m n := by
    simp only [Int.ofNat_eq_coe, Int.ofNat_succ, Int.add_mul, Int.add_comm, Int.one_mul]
  zsmul_neg' m n := by
    simp only [Int.negSucc_coe, Int.ofNat_succ, Int.neg_mul]
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl


instance : AddCommMonoid Int    := by infer_instance
instance : AddMonoid Int        := by infer_instance
instance : Monoid Int           := by infer_instance
instance : CommMonoid Int       := by infer_instance
instance : CommSemigroup Int    := by infer_instance
instance : Semigroup Int        := by infer_instance
instance : AddCommGroup Int     := by infer_instance
instance : AddGroup Int         := by infer_instance
instance : AddCommSemigroup Int := by infer_instance
instance : AddSemigroup Int     := by infer_instance
instance : CommSemiring Int     := by infer_instance
instance : Semiring Int         := by infer_instance
instance instRingInt : Ring Int := by infer_instance
instance : Distrib Int          := by infer_instance

instance instNontrivial : Nontrivial Int where
  exists_pair_ne := ⟨0, 1, Int.zero_ne_one⟩

instance linearOrderedCommRing : LinearOrderedCommRing Int :=
  let instCommRingInt := Int.instCommRing
  let instLinearOrderInt := Int.instLinearOrder
  let instNontrivialInt := Int.instNontrivial
  { instCommRingInt, instLinearOrderInt, instNontrivialInt with
    add_le_add_left := @Int.add_le_add_left,
    mul_pos := @Int.mul_pos, zero_le_one := le_of_lt Int.zero_lt_one }

instance instFloorRing : FloorRing Int where
  floor := id
  ceil := id
  gc_coe_floor a b := by
    rw [Int.cast_id]
    rfl
  gc_ceil_coe a b := by
    rw [Int.cast_id]
    rfl
