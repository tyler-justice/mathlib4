import Mathlib
import Mathlib.GroupTheory.IntegralLattice.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.BilinearForm

open Matrix
open IntegralLattice
open Finset


lemma S : CartanMatrix.E₈.IsSymm := by
  decide


variable (α n : Type*)

theorem isSymm_add_transpose_self [AddCommSemigroup α] (A : Matrix n n α)
  : (A + Aᵀ).IsSymm := by
  exact add_comm _ _


#check ![1,2,3,4,5,6,7,8]


def B := Matrix.toBilin' CartanMatrix.E₈

lemma E8_inner : Inner ℤ (Fin 8 → ℤ) := ⟨fun x y => B x y⟩
example : AddCommGroup (Fin 8 → ℤ) := by exact Pi.addCommGroup

#check Neg (Fin 8 → ℤ)

#check Inner


instance : IntegralLattice (Fin 8 → ℤ) where
  inner := fun x y => B x y
  add := Pi.addCommGroup.add
  add_assoc := Pi.addCommGroup.add_assoc
  zero := Pi.addCommGroup.zero
  zero_add := Pi.addCommGroup.zero_add
  add_zero := Pi.addCommGroup.add_zero
  nsmul := Pi.addCommGroup.nsmul
  nsmul_zero := Pi.addCommGroup.nsmul_zero
  nsmul_succ := Pi.addCommGroup.nsmul_succ
  neg := Pi.addCommGroup.neg
  sub := Pi.addCommGroup.sub
  sub_eq_add_neg := Pi.addCommGroup.sub_eq_add_neg
  zsmul := Pi.addCommGroup.zsmul
  zsmul_zero' := Pi.addCommGroup.zsmul_zero'
  zsmul_succ' := Pi.addCommGroup.zsmul_succ'
  zsmul_neg' := Pi.addCommGroup.zsmul_neg'
  add_left_neg := Pi.addCommGroup.add_left_neg
  add_comm := Pi.addCommGroup.add_comm
  free := by exact Module.Free.function (Fin 8) ℤ ℤ
  finite := by exact Module.Finite.pi
  add_inner := by intro x y z ; simp [B]
  inner_sym := by intro x y ; sorry
  inner_self := by intro x ; sorry
  inner_self_eq_zero := sorry
/--/  inner := sorry --(fun x y => B x y)
  add := by exact Pi.addCommGroup.add
  add_assoc := by exact Pi.addCommGroup.add_assoc
  zero := by exact Pi.addCommGroup.zero
  zero_add := by exact Pi.addCommGroup.zero_add
  add_zero := by exact Pi.addCommGroup.add_zero
  nsmul := by exact Pi.addCommGroup.nsmul
  neg := by exact Pi.addCommGroup.neg
  zsmul := by exact Pi.addCommGroup.zsmul
  add_left_neg := by exact Pi.addCommGroup.add_left_neg
  add_comm := by exact Pi.addCommGroup.add_comm
  free := by exact Pi.addCommGroup
  finite := by exact Pi.addCommGroup
  add_inner := sorry
  inner_sym := sorry
  inner_self := sorry
  inner_self_eq_zero := sorry
-/




theorem unimodular : (det CartanMatrix.E₈ = -1) ∨ (det CartanMatrix.E₈ = 1):= by
   sorry



variable (n m : ℕ)

@[simp] lemma cons_val_five (x : α) (u : Fin m.succ.succ.succ.succ.succ → α) :
    vecCons x u 5 = vecHead (vecTail ( vecTail ( vecTail (vecTail u)))) :=
  rfl

@[simp] lemma cons_val_six (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ  → α) :
    vecCons x u 6 = vecHead (vecTail ( vecTail ( vecTail ( vecTail ( vecTail u))))) :=
  rfl

@[simp] lemma cons_val_seven (x : α) (u : Fin m.succ.succ.succ.succ.succ.succ.succ  → α) :
    vecCons x u 7 = vecHead (vecTail ( vecTail ( vecTail ( vecTail ( vecTail ( vecTail u)))))) :=
  rfl



theorem is_even (x : Fin 8 → ℤ) : ∃ (n : ℤ), B x x = 2*n := by sorry

/-
  rw [B]
  rw [Matrix.toBilin'_apply CartanMatrix.E₈ x x]
  have aux1 :
     ∑ i : Fin 8, ∑ j : Fin 8, x i * CartanMatrix.E₈ i j * x j =
     ∑ i : Fin 8, x i * (∑ j : Fin 8,  CartanMatrix.E₈ i j * x j) := by
     simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [aux1]
  have aux2 : ∑  i : Fin 8, x i *(∑  j : Fin 8, CartanMatrix.E₈ i j * x j) =
      ∑ i : Fin 8, x i * CartanMatrix.E₈ i i * x i +
      2*(∑ i : Fin 8,
      ∑ j : (univ : Finset (Fin 8)).filter (λ j => i.val < j.val),
       x i * CartanMatrix.E₈ i j * x j)
      := by
        apply Finset.sum_congr
-/


#check range 7
--  rw [Fin.sum_univ_castSucc]

/-
  rw [Fin.sum_univ_eight]
  nth_rw 1  [Fin.sum_univ_eight]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1  [Fin.sum_univ_eight]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1  [Fin.sum_univ_eight]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1  [Fin.sum_univ_eight]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [mul_add]
  nth_rw 1 [CartanMatrix.E₈,of_apply]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈,of_apply]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  nth_rw 1 [CartanMatrix.E₈]
  simp
  simp only [cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
   cons_val_seven]
  rw [Fin.succ_zero_eq_one, zero_add]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_eight]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  simp
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_eight]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  simp
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_eight]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_eight]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  simp
  rw [Fin.sum_univ_eight]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  simp
  rw [Fin.sum_univ_eight]
  simp only [Fin.isValue, Int.reduceNeg, cons_val_zero, cons_val_one, head_cons, zero_mul, add_zero,
    cons_val_two, tail_cons, neg_mul, one_mul, cons_val_three, cons_val_four,cons_val_five, cons_val_six,
    cons_val_seven]
  have aux2 : Fin.succ (2: Fin 8) = 3 := rfl
  rw [aux2]



example :  Fin.succ (3:Fin 8) = 4 := rfl



#eval  CartanMatrix.E₈ 0 0





-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Data.Finset.NatAntidiagonal




open Module


def E8 : IntegralLattice (Fin 8 → ℤ) :=
  {
    (Inner := B _ _,
     )
    free  := exact Pi.addCommGroup
    finite := exact Finite.pi
    add_inner := by sorry
    inner_sym := by sorry
    inner_self := by sorry
    inner_self_eq_zero := by sorry
    }


def E8_comm : AddCommGroup (Fin 8 → ℤ) := by exact Pi.addCommGroup

def E8_inner : Inner ℤ (Fin 8 → ℤ) := by sorry

def E8_finite : Finite ℤ (Fin 8 → ℤ) := by  exact Finite.pi

-/
