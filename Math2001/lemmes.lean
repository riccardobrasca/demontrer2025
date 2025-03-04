/-

`lemma ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b`

`lemma ne_of_gt {a b : ℝ} (h : a > b) : a ≠ b`

`lemma le_antisymm {a b : ℝ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b`

`lemma le_or_succ_le {n a : ℤ} : n ≤ a ∨ a+1 ≤ n`

`lemma eq_zero_or_eq_zero_of_mul_eq_zero {a b : ℝ}  (h : a * b = 0) : a = 0 ∨ b = 0`

`lemma ne_of_lt {a b : ℝ} (h : a < b) : a ≠ b`

`lemma abs_le_of_sq_le_sq' {a b : ℝ} (h1 : a ^ 2 ≤ b ^ 2) (h2 : 0 ≤ b) : -b ≤ a ∧ a ≤ b`

`lemma le_or_gt (x y : ℝ) : x ≤ y ∨ x > y`

`lemma abs_le_of_sq_le_sq' {a b : ℝ} (h1 : a ^ 2 ≤ b ^ 2) (h2 : 0 ≤ b) : -b ≤ a ∧ a ≤ b`

`lemma mul_eq_zero {a b : ℝ} : a * b = 0 ↔ a = 0 ∨ b = 0`

`lemma not_lt_of_ge {a b : ℝ} (h : a ≥ b) : ¬a < b`

`lemma not_le_of_gt {a b : ℝ} (h : a > b) : ¬a ≤ b`

`lemma lt_trichotomy (x y : ℝ) : x < y ∨ x = y ∨ x > y`

`lemma comp_apply : (g ∘ f) x = g (f x)`

-/
