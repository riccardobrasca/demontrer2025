import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

open Function


/- SUJET VERSION A-/

/- ATTENTION : IL FAUT METTRE LE FICHIER SUR MOODLE -/

/- exercices OR (1 + 1 points) -/

example {x : ℝ} (hx : 3 * x + 2 = 5) : x = 1 ∨ x = 4 := by
  sorry
  done

 example {x : ℝ} (h : x = -1 ∨ x = 2) : x ^ 2 - x - 2 = 0 := by
  sorry
  done


/- exercices AND (1 + 1 points) -/

example {m n : ℤ} (H : n ≤ 5 ∧ m - 1 ≤ n) : m ≤ 7 := by
  sorry
  done

example {a : ℚ} (h : a - 2 ≥ 8) : a ≥ 5 ∧ 2 * a ≥ 12 := by
  sorry
  done


/- exercice EXISTS (1 point) -/

example : ∀ n : ℤ, ∃ m : ℤ, n + m = 2 := by
  sorry
  done


/- exercice CONTRADICTION (1 point) -/

example {x : ℤ} (h2 : x ≥ 4) (h : x + 8 = 6) : x < 20 := by
  sorry
  done


/- exercice INDUCTION (4 points) -/

example : ∀ n, (-1)^n = 1 ∨ (-1)^n = -1 := by
  sorry
  done



/- exercice INJECTIVE (5 points) -/

example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ 2*(f x + 1)) := by
  sorry
  done



/- exercice SURJECTIVE (5 points) -/

example : ¬ Surjective (fun (x : ℤ) ↦ 4*x) := by
  sorry
  done



/- exercice (2 POINTS DE BONUS) -/

example : ∀ (f g : ℚ → ℚ), Injective f ∧ Injective g → Injective (f ∘ g) := by
  sorry
  done

/- ATTENTION : IL FAUT METTRE LE FICHIER SUR MOODLE -/
