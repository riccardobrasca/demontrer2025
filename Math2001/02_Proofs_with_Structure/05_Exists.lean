/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- le_or_gt (x y : ℝ) : x ≤ y ∨ x > y

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra
  done


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : x * t < x * 0 := by
      calc
        x*t < 0 := by addarith [hxt]
        _ = x*0 := by ring
    have hx' : x ≥ 0 := by addarith [hx]
    cancel x at hxt'
    apply ne_of_lt
    apply hxt'
  done

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers
  done

example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra
  done

example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers
  done

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1
  use a
  ring
  done

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  · calc
      p = (p+p)/2 := by ring
      _ < (p+q)/2 := by rel [h]
  · calc
      (p+q)/2 < (q+q)/2 := by rel [h]
      _ = q := by ring
  done

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  · numbers
  · constructor
    · numbers
    · constructor
      numbers
      numbers
  done

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers
  done

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 2, 9
  numbers
  done

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.5
  constructor
  · numbers
  · numbers
  done

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4, 3
  numbers
  done

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1/2
  calc
    (x+1/2)^2 = x^2 + 1/4 + x := by ring
    _ > x := by extra
  done

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have h1 : a*t-t < a-1 := by addarith [ha]
  have h2 : t*(a-1) < 1*(a-1) := by
    calc
      t*(a-1) = a*t-t := by ring
      _ < a-1 := h1
      _ = 1*(a-1) := by ring
  have h3 := le_or_gt 1 a
  obtain hale | hagt := h3
  · have ha1 : a-1 ≥ 0 := by addarith [hale]
    cancel a-1 at h2
    apply ne_of_lt
    assumption
  · have ha1 : 1-a > 0 := by addarith [hagt]
    have ha2 : 1*(1-a) < t*(1-a) := by
      calc
        1*(1-a) = -(1*(a-1)) := by ring
        _ < -(t*(a-1)) := by rel [h2]
        _ = t*(1-a) := by ring
    cancel 1-a at ha2
    apply ne_of_gt
    assumption
  done

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have h1 := le_or_succ_le a 2
  obtain h1 | h1 := h1
  · apply ne_of_lt
    calc
      m = 2 * a := by rw [ha]
      _ ≤ 2 * 2 := by rel [h1]
      _ < 5 := by numbers
  · apply ne_of_gt
    calc
      m = 2 * a := by rw [ha]
      _ ≥ 2 * 3 := by rel [h1]
      _ > 5 := by numbers
  done

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  have h := le_or_succ_le n 0
  obtain hn | hn := h
  · use 2
    calc
      n*2+7 ≤ 0*2+7 := by rel [hn]
      _ ≤ 2*2^3 := by numbers
  · use n+1
    calc
      2 * (n + 1) ^ 3 = 2*n^3+5*n^2+5*n-5+(n*(n+1)+7) := by ring
      _ ≥ 2*1^3+5*1^2+5*1-5+(n*(n+1)+7) := by rel [hn]
      _ = 7+(n*(n+1)+7) := by ring
      _ ≥ n*(n+1)+7 := by extra
  done

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (-a+b+c)/2, (a-b+c)/2, (a+b-c)/2
  constructor
  · addarith [ha]
  constructor
  · addarith [hb]
  constructor
  addarith [hc]
  constructor
  · ring
  constructor
  · ring
  ring
  done
