/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Equiv
import Mathlib.LinearAlgebra.Dimension.Finrank

universe u

open IntegralLattice
open FiniteDimensional

/-- The Leech lattice is the unique even, unimodular integral lattice of rank 24
  such that the norm of any nonzero vector is at least 4.
-/
class LeechLattice (Λ : Type*) extends IntegralLattice Λ where
  (even : IsEven Λ)
  (unimodular : IsUnimodular Λ)
  (rank_eq_24 : finrank ℤ Λ = 24)
  (min_norm : ∀ (x : Λ), x ≠ 0 → ⟪x, x⟫_ℤ ≥ 4)

namespace LeechLattice

variable (Λ : Type*) [LeechLattice Λ]

theorem unique (Λ₁ Λ₂ : Type*) [LeechLattice Λ₁] [LeechLattice Λ₂]:
  Nonempty (Λ₁ ≃ₗ Λ₂) := sorry

theorem exists_leech : ∃ (Λ : Type u), Nonempty (LeechLattice Λ) := sorry

instance (n : ℕ) : Finite {x: Λ | ⟪x, x⟫_ℤ = n} := sorry
instance (n : ℕ) : Finite {x: Λ // ⟪x, x⟫_ℤ = n} := sorry

-- Lemma's about cardinality of vectors of norms 2, 4, 6 and 8:
lemma card_norm_2 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 2} = 0 := by
  rw [Nat.card_eq_zero]
  left
  simp
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp at hx
  · have := min_norm x hx0
    linarith

lemma card_norm_4 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 4} = 196560 := sorry
lemma card_norm_6 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 6} = 16773120 := sorry
lemma card_norm_8 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 8} = 398034000 := sorry

end LeechLattice
