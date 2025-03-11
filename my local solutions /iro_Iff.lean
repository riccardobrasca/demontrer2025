/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers
  done

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  · intro h
    have hx : (x+3)*(x-2) = 0 := by
      calc (x+3)*(x-2) = x^2 + x - 6 := by ring
        _ = 0 := by rw [h]
      done
    have hh : x+3=0 ∨ x-2 =0 := by apply eq_zero_or_eq_zero_of_mul_eq_zero hx
    obtain h1 | h2 := hh
    · left
      addarith [h1]
    · right
      addarith [h2]
  · intro h
    obtain h1 | h2 := h
    · rw [h1]
      numbers
    · rw [h2]
      numbers
    done


example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  intro h
  have H : a ^ 2 - 5 * a + 6 = 0 := by
    apply le_antisymm
    · addarith [h]
    · obtain Ha | Ha := le_or_succ_le a 2
      · calc
          a^2-5*a+6 = (a-2)^2-a+2 := by ring
            _ ≥ -a+2 := by extra
            _ ≥ -2+2 := by rel [Ha]
            _ ≥ 0 := by numbers
      · calc
            a^2-5*a+6 = (a-3)^2+a-3 := by ring
            _ ≥ (3-3)^2+3-3 := by rel [Ha]
            _ ≥ 0 := by numbers
  have hh : (a-2)*(a-3)=0 := by
    calc (a-2)*(a-3) = a ^ 2 - 5 * a + 6 := by ring
      _ = 0 := by rw [H]
    done
  have hhh : a-2=0 ∨ a-3 =0 := by apply eq_zero_or_eq_zero_of_mul_eq_zero hh
  obtain h1 | h2 := hhh
  · left
    addarith [h1]
  · right
    addarith [h2]
  · intro h
    obtain h1 | h2 := h
    · rw [h1]
      numbers
    · rw [h2]
      numbers
    done



/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  · intro h
    calc x = (2*x)/2 - (1/2) + (1/2) := by ring
      _  = (2*x-1)/2 + 1/2 := by ring
      _ = 11/2 + 1/2 := by rw [h]
      _ = 6 := by numbers
  · intro h
    rw [h]
    numbers



example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  sorry
  done
