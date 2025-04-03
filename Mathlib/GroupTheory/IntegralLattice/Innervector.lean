import Mathlib

open Matrix

-- 階数 2 の自由 ℤ 加群
def R2 := Fin 2 → ℤ

-- 内積, というか対称双線形形式の定義

def H := !![(0:ℤ), (1:ℤ);(1:ℤ), (0:ℤ)] -- 2x2行列


def B := Matrix.toBilin' H


#eval (H 0 0)*(H 1 1) - (H 1 0)*(H 0 1)

-- set_option trace.Meta.Tactic.simp true

theorem is_even (x : R2) : ∃ (n : ℤ), B x x = 2*n := by
  use x 0 * x 1
  rw [B]
  rw [Matrix.toBilin'_apply H x x]
  simp
  calc
    _ = x 0 * 0 * x 0 + x 0 * 1 * x 1 + (x 1 * 1 * x 0 + x 1 * 0 * x 1) 
        :=  rfl 
    _ = x 0 * x 1 + (x 1 * x 0) := by ring_nf 
    _  = 2 * (x 0 * x 1) := by ring


theorem unimodular : (det H = -1) ∨ (det H = 1):= by
  left
  rw [det_fin_two]
  exact rfl 
