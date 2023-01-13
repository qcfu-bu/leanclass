import Mathlib.Tactic.Linarith

def hello := "world"

def a : ℕ → ℤ 
| 0 => 2
| 1 => 5
| n + 2 => 5 * a (n + 1) - 6 * a n 

#check Nat.two_step_induction

lemma helper (n : ℕ) : a (n + 2) = 5 * a (n + 1) - 6 * a n := rfl

lemma foo (n : ℕ) : a n = 2 ^ n + 3 ^ n := by 
  induction' n using Nat.two_step_induction with n h1 h2
  . rfl
  . rfl 
  simp [Nat.succ_eq_add_one] at *
  calc
    a (n + 2) 
      = (5 : ℤ) * (2 ^ (n + 1) + 3 ^ (n + 1)) - 
          6 * (2 ^ n + 3 ^ n) := by linarith [helper n]
    _ = (2 : ℤ) ^ (n + 2) + 3 ^ (n + 2) := by ring

def odd (k : ℤ) : Prop := ∃ a, k = 2 * a + 1

lemma bar2 (n : ℕ) : odd (a (n + 1)) := by
  induction' n with n h1 h2
  . use 2
    rfl
  cases' h1 with k hk
  use 5*k - 3*a n + 2
  rw [helper]
  linarith

lemma bar (n : ℕ) : (n ≥ 1) → odd (a n) := by
  induction' n using Nat.two_step_induction with n h1 h2
  . norm_num
  . intro h
    use 2
    rfl
  simp only [Nat.succ_eq_add_one] at *

/-
    calc
      a (n + 2) 
      -- = 5 * a (n + 1) - 6 * a n := helper n
       = (5 : ℤ) * (2 ^ (n + 1) + 3 ^ (n + 1)) - 
        6 * (2 ^ n + 3 ^ n) := by linarith [helper n]
      -- _ = (5 : ℤ) * (2 * 2^n + 3 * 3^n) - 6 * (2 ^ n + 3 ^ n) := by ring
      -- _ = ((5*2 - 6) : ℤ) * 2^n + (5*3 - 6)*3^n := by ring
      -- _ = (4 : ℤ) * 2^n + 9 * 3^n := by ring
      _ = (2 : ℤ) ^ (n + 2) + 3 ^ (n + 2) := by ring

-/