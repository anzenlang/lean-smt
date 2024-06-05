import Mathlib.Data.Real.Basic

import Smt.Util.Mathlib.Algebra
import Smt.Util.Mathlib.Covariant
import Smt.Util.Mathlib.Group



namespace Smt



private noncomputable def instLor : _root_.LinearOrderedRing Real := inferInstance

noncomputable instance LinearOrderedRing.instReal : LinearOrderedRing Real where
  le_refl := instLor.le_refl
  le_trans := instLor.le_trans
  le_antisymm := instLor.le_antisymm
  le_total := instLor.le_total
  decidableLE := instLor.decidableLE
  decidableLT := instLor.decidableLT
  lt_iff_le_not_le := instLor.lt_iff_le_not_le
  npow := instLor.npow
  npow_zero := instLor.npow_zero
  npow_succ := instLor.npow_succ
  sub_eq_add_neg := instLor.sub_eq_add_neg
  add_assoc := instLor.add_assoc
  zero_add := instLor.zero_add
  add_zero := instLor.add_zero
  nsmul := instLor.nsmul
  nsmul_zero := instLor.nsmul_zero
  nsmul_succ := instLor.nsmul_succ
  add_comm := instLor.add_comm
  left_distrib := instLor.left_distrib
  right_distrib := instLor.right_distrib
  zero_mul := instLor.zero_mul
  mul_zero := instLor.mul_zero
  mul_assoc := instLor.mul_assoc
  one_mul := instLor.one_mul
  mul_one := instLor.mul_one
  zsmul := instLor.zsmul
  zsmul_zero' := instLor.zsmul_zero'
  zsmul_succ' := instLor.zsmul_succ'
  zsmul_neg' := instLor.zsmul_neg'
  add_left_neg := instLor.add_left_neg
  add_le_add_left := instLor.add_le_add_left
  exists_pair_ne := instLor.exists_pair_ne
  zero_le_one := instLor.zero_le_one
  mul_pos := instLor.mul_pos

noncomputable instance OrderedAddCommMonoid.instReal : OrderedAddCommMonoid Real where
  add_le_add_left := Real.orderedAddCommMonoid.add_le_add_left


-- instance FloorRing.instReal : FloorRing Real where



instance instCovariantRealAddLT : CovariantClass Real Real (· + ·) (· < ·) where
  elim :=
    (Real.add_lt_add_iff_left · |>.mpr)
instance instCovariantRealSwapAddLT : CovariantClass Real Real (swap (· + ·)) (· < ·) where
  elim m := by
    simp
-- #TODO don't leverage mathlib instance
instance instCovariantRealAddLE : CovariantClass Real Real (· + ·) (· ≤ ·) where
  elim :=
    (inferInstance : _root_.CovariantClass Real Real (· + ·) (· ≤ ·)).elim
-- #TODO don't leverage mathlib instance
instance instCovariantRealSwapAddLE : CovariantClass Real Real (swap (· + ·)) (· ≤ ·) where
  elim :=
    (inferInstance : _root_.CovariantClass Real Real (swap (· + ·)) (· ≤ ·)).elim
