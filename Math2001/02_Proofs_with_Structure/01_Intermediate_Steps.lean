/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by addarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw [h1, hb]
    _ = 9 := by ring
  done


example {m n : ℤ} (h1 : m + 3 ≤ 2 * n - 1) (h2 : n ≤ 5) : m ≤ 6 := by
  have h3 : m + 3 ≤ 9 := by
    calc
      m + 3 ≤ 2 * n - 1 := by rel [h1]
      _ ≤ 2 * 5 - 1 := by rel [h2]
      _ = 9 := by numbers
    done
  addarith [h3]
  done


example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith [h1]
  have h4 : r ≤ 3 - s := by addarith [h2]
  calc
    r = (r + r) / 2 := by ring
    _ ≤ (3 - s + (3 + s)) / 2 := by rel [h3, h4]
    _ = 3 := by ring
  done

example {t : ℝ} (h1 : t ^ 2 = 3 * t) (h2 : t ≥ 1) : t ≥ 2 := by
  have h3 : t * t = 3 * t := by
    calc t * t = t ^ 2 := by ring
      _ = 3 * t := by rw [h1]
    done
  cancel t at h3
  addarith [h3]
  done


example {a b : ℝ} (h1 : a ^ 2 = b ^ 2 + 1) (h2 : a ≥ 0) : a ≥ 1 := by
  have h3 : a ^ 2 ≥ 1 ^ 2 := by
    calc
      a ^ 2 = b ^ 2 + 1 := by rw [h1]
      _ ≥ 1 := by extra
      _ = 1 ^ 2 := by ring
    done
  cancel 2 at h3
  done


example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have h1 : x ≤ -1 := by addarith [hx]
  calc
    y ≥ 3-2*x := by addarith [hy]
    _ ≥ 3-2*(-1) := by rel [h1]
    _ > 3 := by numbers
  done

example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ a+b := by addarith [h1]
  have h4 : 0 ≤ b-a := by addarith [h2]
  calc
    a^2 ≤ a^2+(a+b)*(b-a) := by extra
    _ = b^2 := by ring
  done

example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by
  have h1 : 0 ≤ b-a := by addarith [h]
  calc
    a^3 ≤ a^3+((b-a)*((b-a)^2+3*(b+a)^2))/4 := by extra
    _ = b^3 := by ring
  done

/-! # Exercises -/


example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x*(x+2)=2*(x+2) := by
    calc
      x*(x+2) = x^2+2*x := by ring
      _ = 4+2*x := by rw [h1]
      _ = 2*(x+2) := by ring
    done
  cancel (x+2) at h3
  done

example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 : (n-2)^2=0^2 := by
    calc
      (n-2)^2 = n^2+4-4*n := by ring
      _ = 4*n-4*n := by rw [hn]
      _ = 0^2 := by ring
    done
  cancel 2 at h1
  addarith [h1]
  done

example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have hxy : 0 < x*y := by
    calc
      0 < 1 := by numbers
      _ = x*y := by rw [h]
    done
  cancel x at hxy
  calc
    y = 1*y := by ring
    _ ≤ x*y := by rel [h2]
    _ = 1 := by rw [h]
  done
