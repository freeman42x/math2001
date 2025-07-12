/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


def a (n : ℕ) : ℕ := 2 ^ n


#eval a 20 -- infoview displays `1048576`


def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2


#eval b 7 -- infoview displays `316837008400094222150776738483768236006420971486980607`


example (n : ℕ) : Odd (b n) := by
  simple_induction n with k hk
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by numbers
  · -- inductive step
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring


def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1


example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  simple_induction n with k IH
  · -- base case
    calc
      x 0
        = 5 := by rw [x]
      _ ≡ 1 + 1 * 4 [ZMOD 4] := by numbers
      _ ≡ 1 [ZMOD 4] := by extra
  · -- inductive step
    obtain ⟨m, hm⟩ := IH
    use 2 * m
    calc
      x (k + 1) - 1
        = (2 * x k - 1) - 1 := by rw [x]
      _ = 2 * (x k - 1) := by ring
      _ = 2 * (4 * m) := by rw [hm]
      _ = 4 * (2 * m) := by ring

example (n : ℕ) : x n = 2 ^ (n + 2) + 1 := by
  simple_induction n with k IH
  · -- base case
    calc x 0 = 5 := by rw [x]
      _ = 2 ^ (0 + 2) + 1 := by numbers
  · -- inductive step
    calc x (k + 1) = 2 * x k - 1 := by rw [x]
      _ = 2 * (2 ^ (k + 2) + 1) - 1 := by rw [IH]
      _ = 2 ^ ((k + 1) + 2) + 1 := by ring


def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)


example (n : ℕ) : A n = n * (n + 1) / 2 := by
  simple_induction n with k IH
  · -- base case
    calc A 0 = 0 := by rw [A]
      _ = 0 * (0 + 1) / 2 := by numbers
  · -- inductive step
    calc
      A (k + 1) = A k + (k + 1) := by rw [A]
      _ = k * (k + 1) / 2 + (k + 1) := by rw [IH]
      _ = (k + 1) * (k + 1 + 1) / 2 := by ring



def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n


example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  simple_induction n with k IH
  · -- base case
    intro k hk1 hk
    interval_cases k
  · -- inductive step
    intro d hk1 hk
    obtain hk | hk : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hk
    · -- case 1: `d = k + 1`
      use (k !)
      calc
        (k + 1) !
          = (k + 1) * k ! := by rw [factorial]
        _ = d * k ! := by rw [← hk]
    · -- case 2: `d < k + 1`
      have h1 : d ≤ k := Nat.lt_succ_iff.mp hk
      have h2 : d ∣ k ! := IH d hk1 h1
      obtain ⟨x, hx⟩ := h2
      dsimp [(· ∣ ·)]
      use (k + 1) * x
      calc
        (k + 1) !
          = (k + 1) * k ! := by rw [factorial]
        _ = (k + 1) * (d * x) := by rw [hx]
        _ = d * ((k + 1) * x) := by ring

example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by
  simple_induction n with k ih
  · calc
      (0 + 1) !
        = (0 + 1) * 1 := by rw [factorial, factorial]
      _ = 1 := by numbers
      _ ≥ 2 ^ 0 := by numbers
  · calc
      (k + 1 + 1) !
        = (k + 1 + 1) * (k + 1) ! := by rw [factorial]
      _ ≥ (k + 1 + 1) * 2 ^ k := by rel [ih]
      _ = k * 2 ^ k + 2 * 2 ^ k := by ring
      _ ≥ 2 * 2 ^ k := by extra
      _ = 2 ^ (k + 1) := by ring


/-! # Exercises -/


def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  dsimp [Odd]
  simple_induction n with k ih
  · use 3
    calc
      c 0
        = 7 := by rw [c]
      _ = 2 * 3 + 1 := by numbers
  · obtain ⟨m, hm⟩ := ih
    use 3 * m - 4
    calc
      c (k + 1)
        = 3 * c k - 10 := by rw [c]
      _ = 3 * (2 * m + 1) - 10 := by rw [hm]
      _ = 6 * m - 7 := by ring
      _ = 2 * (3 * m - 4) + 1 := by ring

example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  sorry

def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  sorry

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  sorry

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  sorry

example (n : ℕ) : 0 < n ! := by
  sorry

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  sorry

example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by
  sorry
