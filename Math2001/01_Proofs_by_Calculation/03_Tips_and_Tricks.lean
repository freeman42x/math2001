/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a
      = 2 * b + 5 := by rw[h1]
    _ = 2 * 3 + 5 := by rw[h2]
    _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x
      = (x + 4) - 4 := by ring
    _ = 2 - 4 := by rw[h1]
    _ = -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a
      = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw[h1]
    _ = 4 + 5 * (b + 2 - 2) := by ring
    _ = 4 + 5 * (3 - 2) := by rw[h2]
    _ = 9 := by ring

-- Example 1.3.4
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w
      = (3 * w + 1) / 3 - 1 / 3 := by ring
    _ = 4 / 3 - 1 /3 := by rw [h1]
    _ = 1 := by ring

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x
      = 2 * x + 3 - x - 3 := by ring
    _ = x - x - 3 := by rw[h1]
    _ = -3 := by ring

-- Example 1.3.6
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x
      = (2 * x - y) + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw[h1, h2]
    _ = 5 := by ring

-- Example 1.3.7
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u
      = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
    _ = (4 + 6) / 2 := by rw[h1, h2]
    _ = 5 := by ring

-- Example 1.3.8
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    x
      = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
    _ = (3 * 4 + 4) / 8 := by rw[h1, h2]
    _ = 2 := by ring

-- Example 1.3.9
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3
      = ((a - 3) ^ 2 + 6 * a - 9) - a + 3 := by ring
    _ = (a - 3) ^ 2 + 5 * a - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * ((a - 3) + 3) - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * (a - 3) + 9 := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b) + 9 := by rw[h1]
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1
      = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by ring
    _ = (z ^ 2 - z + 1) * 0 + 3 := by rw[h1]
    _ = 3 := by ring

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y
      = 4 * x - 3 := by rw[h2]
    _ = 4 * 3 - 3 := by rw[h1]
    _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a
      = a - b + b := by ring
    _ = 0 + b := by rw[h]
    _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x
      = x - 3 * y + 3 * y := by ring
    _ = 5 + 3 * y := by rw[h1]
    _ = 5 + 3 * 3 := by rw[h2]
    _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p
      = p - 2 * q + 2 * q := by ring
    _ = 1 + 2 * q := by rw[h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = -1 := by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
    x
      = x + 2 * y - 2 * (y + 1 - 1) := by ring
    _ = 3 - 2 * (3 - 1) := by rw [h1, h2]
    _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p
      = p + 4 * q - 4 * (q - 1 + 1) := by ring
    _ = 1 - 4 * (2 + 1) := by rw[h1, h2]
    _ = -11 := by ring

example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 :=
  calc
    a
      = a + 2 * b + 3 * c - 2 * (b + 2 * c - 2 * c) - 3 * c := by ring
    _ = 7 - 2 * (3 - 2 * 1) - 3 * 1 := by rw[h1,h2,h3]
    _ = 2 := by ring

example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u
      = (4 * u + v) / 4 - v / 4 := by ring
    _ = 3 / 4 - 2 / 4 := by rw[h1,h2]
    _ = 1 / 4 := by ring

example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
    c = 4 * c + 1 - 3 * c - 1 := by ring
    _ = 3 * c - 2 - 3 * c - 1 := by rw[h1]
    _ = -3 := by ring

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  calc
    p = (5 * p - 3) / 2 - (3 * p - 3) / 2 := by ring
    _ = (3 * p + 1) / 2 - (3 * p - 3) / 2 := by rw[h1]
    _ = 2 := by ring

example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
    x = 2 * x + y - (x + y) := by ring
    _ = 4 - 1 := by rw [h1,h2]
    _ = 3 := by ring

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
    a = (1/3) * (a + 2 * b) + (2/3) * (a - b) := by ring
    _ = (1/3) * 4 + (2/3) * 1                 := by rw [h1, h2]
    _ = 2                                     := by ring

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
    u ^ 2 + 3 * u + 1
      = (u + 1 - 1) ^ 2 + 3 * u + 1 := by ring
    _ = (v - 1) ^ 2 + 3 * u + 1 := by rw[h1]
    _ = (v - 1) ^ 2 + 3 * (u + 1 - 1) + 1 := by ring
    _ = (v - 1) ^ 2 + 3 * (v - 1) + 1 := by rw[h1]
    _ = v ^ 2 + v - 1 := by ring

example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
      = (t ^ 2 - 4) * (t ^ 2 + 3 * t + 1) + 10 * t + 2 := by ring
    _ = 0 * (t ^ 2 + 3 * t + 1) + 10 * t + 2 := by rw[ht]
    _ = 10 * t + 2 := by ring

example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
    y
    _ = (y - 2) * (x + 5 - (x + 3)) / 2 + 2 := by ring
    _ = (y - 2) * (x + 5 - 5) / 2 + 2 := by rw[h1]
    _ = 2 - (2 * x - y * x) / 2 := by ring
    _ = 2 - 0 / 2 := by rw [h2]
    _ = 2 := by ring

example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
    p ^ 2 + q ^ 2 + r ^ 2
      = (p + q + r) ^ 2 - 2 * (p * q + p * r + q * r) := by ring
    _ = 0 ^ 2 - 2 * 2 := by rw[h1, h2]
    _ = -4 := by ring
