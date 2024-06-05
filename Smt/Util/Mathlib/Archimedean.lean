import Smt.Util.Mathlib.Field



namespace Smt



-- section LinearOrderedField

-- variable [LinearOrderedField α]

-- theorem archimedean_iff_int_le : Archimedean α ↔ ∀ x : α, ∃ n : Int, x ≤ n :=
--   archimedean_iff_int_lt.trans
--     ⟨fun H x => (H x).imp fun _ => le_of_lt, fun H x =>
--       let ⟨n, h⟩ := H x
--       ⟨n + 1, lt_of_le_of_lt h (Int.cast_lt.2 (lt_add_one _))⟩⟩

-- end LinearOrderedField



-- namespace FloorRing
-- /-- A linear ordered field that is a floor ring is archimedean. -/
-- instance
--   (priority := 100) FloorRing.archimedean
--   (α : Type u) [LinearOrderedField α] [FloorRing α]
-- : Archimedean α := by
--   rw [archimedean_iff_int_le]
--   exact fun x => ⟨ceil x, Int.le_ceil x⟩
-- end FloorRing


-- /-- A linear ordered archimedean ring is a floor ring. This is not an `instance` because in some
-- cases we have a computable `floor` function. -/
-- noncomputable def Archimedean.floorRing
--   (α : Type u)
--   [LinearOrderedRing α] [Archimedean α]
-- : FloorRing α :=
--   FloorRing.ofFloor α (fun a => Classical.choose (exists_floor a)) fun z a =>
--     (Classical.choose_spec (exists_floor a) z).symm

-- -- see Note [lower instance priority]
-- /-- A linear ordered field that is a floor ring is archimedean. -/
-- instance (priority := 100) FloorRing.archimedean
--   (α : Type u) [LinearOrderedField α] [FloorRing α]
-- : Archimedean α := by
--   rw [archimedean_iff_int_le]
--   exact fun x => ⟨⌈x⌉, Int.le_ceil x⟩
-- #align floor_ring.archimedean FloorRing.archimedean
