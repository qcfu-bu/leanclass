import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Existsi
import BrownCs22.Demos.Readme

/- 4 points -/
theorem problem1 {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) :
    (a + b) ^ 2 = 20 :=
  calc (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
  _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
  _ = 20 := by ring

/- 2 points -/
theorem problem2 {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2) : a ≥ 0 := by
  cases' h with b hb
  calc a = b ^ 2 := hb
  _ ≥ 0 := by apply sq_nonneg

theorem you_might_use_this_theorem_in_your_answer :
    1 + 1 = 2 := by
  norm_num

/- 4 points -/
theorem problem3 : ∃ n : ℤ, 12 * n = 84 := by
  existsi 7
  norm_num