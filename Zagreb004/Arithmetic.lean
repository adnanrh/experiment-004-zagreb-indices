import Mathlib

/-!
UNCOMPILED CANDIDATE. These are arithmetic lemmas, not a replacement for the
missing universal graph-to-profile and family-realization arguments.
-/
set_option autoImplicit false

namespace Zagreb004.Arithmetic

/-- The coefficient barrier, with all coefficients scaled by 60. -/
theorem coefficient_barrier (a b A B C : ℚ)
    (ha : 0 < a) (hb : 0 < b) (hs : a + b ≤ 69)
    (hA : 35 ≤ A) (hB : 35 ≤ B) (hC : 0 ≤ C)
    (hgap : A * a + B * b + C < 2 * a * b) : False := by
  have hAa : 35 * a ≤ A * a := mul_le_mul_of_nonneg_right hA ha.le
  have hBb : 35 * b ≤ B * b := mul_le_mul_of_nonneg_right hB hb.le
  have hS : 0 < a + b := add_pos ha hb
  have hbound : (a + b) * (a + b) ≤ 69 * (a + b) :=
    mul_le_mul_of_nonneg_right hs hS.le
  nlinarith [sq_nonneg (a - b)]

/-- Pattern II cannot fit into 46 vertices. -/
theorem patternII_impossible (a b : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hn : 21 * a + 20 * b + 85 ≤ 1380)
    (hgap : 16 * a + 15 * b + 60 < a * b) : False := by
  have ha15 : 15 < a := by
    by_contra h
    have hle : a ≤ 15 := le_of_not_gt h
    have := mul_le_mul_of_nonneg_right hle hb
    nlinarith
  have hb16 : 16 < b := by
    by_contra h
    have hle : b ≤ 16 := le_of_not_gt h
    have := mul_le_mul_of_nonneg_left hle ha
    nlinarith
  let X : ℚ := 21 * (a - 15)
  let Y : ℚ := 20 * (b - 16)
  have hX : 0 < X := by dsimp [X]; linarith
  have hY : 0 < Y := by dsimp [Y]; linarith
  have hsum : X + Y ≤ 660 := by dsimp [X, Y]; linarith
  have hprod : 126000 < X * Y := by dsimp [X, Y]; nlinarith
  have hsum0 : 0 ≤ X + Y := le_of_lt (add_pos hX hY)
  have hsquare : (X + Y) * (X + Y) ≤ 660 * (X + Y) :=
    mul_le_mul_of_nonneg_right hsum hsum0
  nlinarith [sq_nonneg (X - Y)]

/-- Pattern I, including the incidence-integrality constraints. -/
theorem patternI_unique (a b n2 n3 n5 : ℕ)
    (h5 : a = 5 * n5) (h2 : a + 1 = 2 * n2)
    (h3 : 2 * b + 1 = 3 * n3)
    (hn : 21 * a + 20 * b + 25 ≤ 1380)
    (hgap : 16 * a + 15 * b < a * b) : a = 35 ∧ b = 31 := by
  have ha15 : 15 < a := by
    by_contra h
    have hle : a ≤ 15 := by omega
    have hmul : a * b ≤ 15 * b := Nat.mul_le_mul_right b hle
    omega
  have hb16 : 16 < b := by
    by_contra h
    have hle : b ≤ 16 := by omega
    have hmul : a * b ≤ a * 16 := Nat.mul_le_mul_left a hle
    omega
  have hb19 : 19 ≤ b := by omega
  have ha46 : a ≤ 46 := by omega
  have cases_a : a = 25 ∨ a = 35 ∨ a = 45 := by omega
  rcases cases_a with h | h | h
  · rw [h] at hn hgap
    omega
  · constructor
    · exact h
    · rw [h] at hn hgap
      omega
  · rw [h] at hn hgap
    omega

/-- Closed forms; these definitions do not construct a graph. -/
def familyOrder (k l : ℚ) : ℚ := (7 * k + 4 * l + 3) / 2
def familySize (k l : ℚ) : ℚ := 5 * k + 3 * l + 2
def familyM1 (k l : ℚ) : ℚ := 35 * k + 18 * l + 11
def familyM2 (k l : ℚ) : ℚ := 50 * k + 27 * l + 15

def familyGap (k l : ℚ) : ℚ :=
  familySize k l * familyM1 k l - familyOrder k l * familyM2 k l

theorem family_gap_identity (k l : ℚ) :
    familyGap k l = (k * l - 5 * k - 3 * l - 1) / 2 := by
  unfold familyGap familySize familyM1 familyOrder familyM2
  ring

theorem even_order_identity (n : ℚ) :
    familyOrder 7 ((n - 26) / 2) = n := by
  unfold familyOrder
  ring

theorem odd_order_identity (n : ℚ) :
    familyOrder 5 ((n - 19) / 2) = n := by
  unfold familyOrder
  ring

theorem even_gap_identity (n : ℚ) :
    familyGap 7 ((n - 26) / 2) = n - 44 := by
  rw [family_gap_identity]
  ring

theorem odd_gap_identity (n : ℚ) :
    familyGap 5 ((n - 19) / 2) = (n - 45) / 2 := by
  rw [family_gap_identity]
  ring

theorem even_gap_positive (n : ℚ) (hn : 46 ≤ n) :
    0 < familyGap 7 ((n - 26) / 2) := by
  rw [even_gap_identity]
  linarith

theorem odd_gap_positive (n : ℚ) (hn : 47 ≤ n) :
    0 < familyGap 5 ((n - 19) / 2) := by
  rw [odd_gap_identity]
  linarith

/-- All orders have integer parameters with positive predicted gap.
This does NOT assert that those parameters have been realized by formal graphs. -/
theorem all_orders_parameters (n : ℕ) (hn : 46 ≤ n) :
    ∃ k l : ℕ,
      3 ≤ k ∧ k % 2 = 1 ∧ 3 ≤ l ∧
      7 * k + 4 * l + 3 = 2 * n ∧
      5 * k + 3 * l + 1 < k * l := by
  by_cases he : n % 2 = 0
  · refine ⟨7, (n - 26) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨5, (n - 19) / 2, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Zagreb004.Arithmetic
