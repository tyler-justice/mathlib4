/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Leech.Basic
import Mathlib.GroupTheory.IntegralLattice.Leech.Cross
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.GroupAction.Iwasawa

open IntegralLatticeAut

variable (Λ : Type*) [LeechLattice Λ]

-- The Conway-0 group is the automorphism group of the Leech lattice.
-- We use the IntegralLatticeAut structure to construct the variable.
abbrev Conway₀ := IntegralLatticeAut Λ

-- The Conway-1 group is the Conway-0 group modulo its center.
abbrev Conway₁ := Conway₀ Λ ⧸ (Subgroup.center (Conway₀ Λ))

namespace Conway₁

def iwasawa : IwasawaStructure (Conway₀ Λ) (Cross Λ) where
    T := sorry
    is_comm := sorry
    is_conj := sorry
    is_generator := sorry

lemma nontrivial : Nontrivial (Conway₁ Λ) := by
  apply Nontrivial.mk
  let id : Conway₁ Λ := 1
  -- TODO: Exhibit a non-identity element in the Conway-1 group.
  have hnt : ∃ x : Conway₁ Λ, id ≠ x := sorry
  use id

lemma quasipreprimitive : IsQuasipreprimitive (Conway₀ Λ) (Cross Λ) := sorry

lemma perfect : commutator (Conway₀ Λ) = ⊤ := sorry

-- TODO: Define the action of the Conway-1 group on the crosses.
-- lemma faithfull : FaithfulSMul (Conway₁ Λ) (Cross Λ) := sorry

-- The Conway-1 group is a simple group.
instance simple : IsSimpleGroup (Conway₀ Λ) := by
  -- TODO: Use the Iwasawa structure by ACL and apply the isSimpleGroup theorem.
  sorry

end Conway₁
