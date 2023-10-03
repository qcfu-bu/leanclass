import Mathlib.Data.Rat.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Existsi
import BrownCs22.Demos.Readme

/- 4 points -/
theorem problem1 {a b : ℚ} (h1 : a - b = 4) (h2 : a * b = 1) :
    (a + b) ^ 2 = 20 := sorry

/- 2 points -/
theorem problem2 {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2) : a ≥ 0 := sorry

theorem you_might_use_this_theorem_in_your_answer :
    1 + 1 = 2 := sorry

/- 4 points -/
theorem problem3 : ∃ n : ℤ, 12 * n = 84 := sorry