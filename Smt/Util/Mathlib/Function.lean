/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

namespace Smt



abbrev Function.swap {φ : α → β → Sort u₃} (f : ∀ x y, φ x y) : ∀ y x, φ x y :=
  fun y x => f x y

export Function (swap)
