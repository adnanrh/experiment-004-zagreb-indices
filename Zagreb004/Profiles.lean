import Zagreb004.Arithmetic

/-!
UNCOMPILED CANDIDATE. This is a theorem about natural-number edge profiles
with explicitly stated incidence and cut constraints. It is NOT yet a theorem
about every Mathlib graph: the graph-to-profile reduction remains to be written.
Coefficients are scaled by 60 to avoid fractional inequalities in the reduction.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Zagreb004.Profiles

structure Counts where
  e22 : ℕ
  e23 : ℕ
  e24 : ℕ
  e25 : ℕ
  e33 : ℕ
  e34 : ℕ
  e35 : ℕ
  e44 : ℕ
  e45 : ℕ
  e55 : ℕ
  deriving DecidableEq, Repr

/-- Sixty times the vertex count predicted by reciprocal incidence counting. -/
def order60 (c : Counts) : ℕ :=
  60*c.e22 + 50*c.e23 + 45*c.e24 + 42*c.e25 + 40*c.e33 +
  35*c.e34 + 32*c.e35 + 30*c.e44 + 27*c.e45 + 24*c.e55

def profileSize (c : Counts) : ℕ :=
  c.e22+c.e23+c.e24+c.e25+c.e33+c.e34+c.e35+c.e44+c.e45+c.e55

def profileM1 (c : Counts) : ℕ :=
  4*c.e22+5*c.e23+6*c.e24+7*c.e25+6*c.e33+
  7*c.e34+8*c.e35+8*c.e44+9*c.e45+10*c.e55

def profileM2 (c : Counts) : ℕ :=
  4*c.e22+6*c.e23+8*c.e24+10*c.e25+9*c.e33+
  12*c.e34+15*c.e35+16*c.e44+20*c.e45+25*c.e55

def penaltyA60 (c : Counts) : ℕ :=
  108*c.e22+32*c.e23+6*c.e24+14*c.e34+
  50*c.e35+72*c.e44+150*c.e45+270*c.e55

def penaltyB60 (c : Counts) : ℕ :=
  100*c.e22+30*c.e23+5*c.e24+15*c.e34+
  48*c.e35+70*c.e44+143*c.e45+256*c.e55

def penaltyC60 (c : Counts) : ℕ :=
  20 * c.e22 * c.e23 +
  60 * c.e22 * c.e24 +
  200 * c.e22 * c.e34 +
  308 * c.e22 * c.e35 +
  360 * c.e22 * c.e44 +
  528 * c.e22 * c.e45 +
  756 * c.e22 * c.e55 +
  10 * c.e23 * c.e24 +
  90 * c.e23 * c.e34 +
  162 * c.e23 * c.e35 +
  200 * c.e23 * c.e44 +
  322 * c.e23 * c.e45 +
  494 * c.e23 * c.e55 +
  40 * c.e24 * c.e34 +
  91 * c.e24 * c.e35 +
  120 * c.e24 * c.e44 +
  216 * c.e24 * c.e45 +
  357 * c.e24 * c.e55 +
  9 * c.e34 * c.e35 +
  20 * c.e34 * c.e44 +
  64 * c.e34 * c.e45 +
  143 * c.e34 * c.e55 +
  2 * c.e35 * c.e44 +
  25 * c.e35 * c.e45 +
  80 * c.e35 * c.e55 +
  12 * c.e44 * c.e45 +
  54 * c.e44 * c.e55 +
  15 * c.e45 * c.e55

/-- Positive scaled gap, expressed without natural subtraction. -/
def positiveGap (c : Counts) : Prop :=
  penaltyA60 c * c.e25 + penaltyB60 c * c.e33 + penaltyC60 c <
    2 * c.e25 * c.e33

/-- Two necessary cut conditions, NOT a graph-realizability claim. -/
def cutConditions (c : Counts) : Prop :=
  (0 < c.e25 → 0 < c.e33 → 0 < c.e23 + c.e34 + c.e35) ∧
  (0 < c.e25 → 0 < c.e33 → 0 < c.e23 + c.e24 + c.e35 + c.e45)

def canonical : Counts := ⟨0, 1, 0, 35, 31, 0, 0, 0, 0, 0⟩

/-- An algebraic identity for arbitrary profiles, not an assumed gap formula. -/
theorem gap_identity (c : Counts) :
    (profileSize c : ℚ) * (profileM1 c : ℚ) -
      (order60 c : ℚ) / 60 * (profileM2 c : ℚ) =
    (2 * (c.e25 : ℚ) * (c.e33 : ℚ) -
      (penaltyA60 c : ℚ) * (c.e25 : ℚ) -
      (penaltyB60 c : ℚ) * (c.e33 : ℚ) - (penaltyC60 c : ℚ)) / 60 := by
  unfold profileSize profileM1 profileM2 order60 penaltyA60 penaltyB60 penaltyC60
  push_cast
  ring

/-- Complete intended arithmetic-profile classification.
The incidence and cut hypotheses must still be derived from arbitrary graphs. -/
theorem profile_threshold (c : Counts) (n2 n3 n4 n5 : ℕ)
    (h2 : 2*c.e22+c.e23+c.e24+c.e25 = 2*n2)
    (h3 : c.e23+2*c.e33+c.e34+c.e35 = 3*n3)
    (h4 : c.e24+c.e34+2*c.e44+c.e45 = 4*n4)
    (h5 : c.e25+c.e35+c.e45+2*c.e55 = 5*n5)
    (hsmall : order60 c ≤ 2760)
    (hcuts : cutConditions c) (hpos : positiveGap c) : c = canonical := by
  have ha : 0 < c.e25 := by
    by_contra h
    have hz : c.e25 = 0 := by omega
    simp [positiveGap, hz] at hpos
  have hb : 0 < c.e33 := by
    by_contra h
    have hz : c.e33 = 0 := by omega
    simp [positiveGap, hz] at hpos
  have hs : c.e25 + c.e33 ≤ 69 := by
    have h := hsmall
    unfold order60 at h
    omega
  have hAB : penaltyA60 c < 35 ∨ penaltyB60 c < 35 := by
    by_cases hA : penaltyA60 c < 35
    · exact Or.inl hA
    · right
      by_contra hB
      have hA' : 35 ≤ penaltyA60 c := by omega
      have hB' : 35 ≤ penaltyB60 c := by omega
      exact Arithmetic.coefficient_barrier
        (c.e25 : ℚ) (c.e33 : ℚ) (penaltyA60 c : ℚ)
        (penaltyB60 c : ℚ) (penaltyC60 c : ℚ)
        (by exact_mod_cast ha) (by exact_mod_cast hb)
        (by exact_mod_cast hs) (by exact_mod_cast hA')
        (by exact_mod_cast hB') (by positivity)
        (by
          have hnat : penaltyA60 c * c.e25 + penaltyB60 c * c.e33 +
              penaltyC60 c < 2*c.e25*c.e33 := hpos
          exact_mod_cast hnat)
  have hz22 : c.e22 = 0 := by
    rcases hAB with h | h <;>
      simp only [penaltyA60, penaltyB60] at h <;> omega
  have hz35 : c.e35 = 0 := by
    rcases hAB with h | h <;>
      simp only [penaltyA60, penaltyB60] at h <;> omega
  have hz44 : c.e44 = 0 := by
    rcases hAB with h | h <;>
      simp only [penaltyA60, penaltyB60] at h <;> omega
  have hz45 : c.e45 = 0 := by
    rcases hAB with h | h <;>
      simp only [penaltyA60, penaltyB60] at h <;> omega
  have hz55 : c.e55 = 0 := by
    rcases hAB with h | h <;>
      simp only [penaltyA60, penaltyB60] at h <;> omega
  have patterns :
      (c.e23 = 1 ∧ c.e24 = 0 ∧ c.e34 = 0) ∨
      (c.e23 = 0 ∧ c.e24 = 3 ∧ c.e34 = 1) := by
    by_cases hz23 : c.e23 = 0
    · right
      have hp : 0 < c.e24 := by
        have h := hcuts.2 ha hb
        simp [hz23, hz35, hz45] at h
        exact h
      have hq : 0 < c.e34 := by
        have h := hcuts.1 ha hb
        simp [hz23, hz35] at h
        exact h
      have hfour : c.e24 + c.e34 = 4*n4 := by
        simpa [hz44, hz45] using h4
      rcases hAB with h | h <;>
        simp [penaltyA60, penaltyB60, hz22, hz23, hz35, hz44, hz45, hz55] at h <;>
        omega
    · left
      have h23 : 0 < c.e23 := by omega
      rcases hAB with h | h <;>
        simp [penaltyA60, penaltyB60, hz22, hz35, hz44, hz45, hz55] at h <;>
        omega
  rcases patterns with ⟨h23, h24, h34⟩ | ⟨h23, h24, h34⟩
  · have horder : 21*c.e25 + 20*c.e33 + 25 ≤ 1380 := by
      have h := hsmall
      simp [order60, hz22, h23, h24, h34, hz35, hz44, hz45, hz55] at h
      omega
    have hgain : 32*c.e25 + 30*c.e33 < 2*c.e25*c.e33 := by
      simpa [positiveGap, penaltyA60, penaltyB60, penaltyC60,
        hz22, h23, h24, h34, hz35, hz44, hz45, hz55] using hpos
    have hgain' : 16*c.e25 + 15*c.e33 < c.e25*c.e33 := by nlinarith
    have h2' : c.e25 + 1 = 2*n2 := by
      simp [hz22, h23, h24] at h2
      omega
    have h3' : 2*c.e33 + 1 = 3*n3 := by
      simp [h23, h34, hz35] at h3
      omega
    have h5' : c.e25 = 5*n5 := by simpa [hz35, hz45, hz55] using h5
    obtain ⟨ha35, hb31⟩ := Arithmetic.patternI_unique
      c.e25 c.e33 n2 n3 n5 h5' h2' h3' horder hgain'
    cases c
    simp_all [canonical]
  · have horder : 21*c.e25 + 20*c.e33 + 85 ≤ 1380 := by
      have h := hsmall
      simp [order60, hz22, h23, h24, h34, hz35, hz44, hz45, hz55] at h
      omega
    have hgain : 32*c.e25 + 30*c.e33 + 120 < 2*c.e25*c.e33 := by
      simpa [positiveGap, penaltyA60, penaltyB60, penaltyC60,
        hz22, h23, h24, h34, hz35, hz44, hz45, hz55] using hpos
    have hgainQ : 16*(c.e25 : ℚ) + 15*(c.e33 : ℚ) + 60 <
        (c.e25 : ℚ)*(c.e33 : ℚ) := by
      have h : 32*(c.e25 : ℚ) + 30*(c.e33 : ℚ) + 120 <
          2*(c.e25 : ℚ)*(c.e33 : ℚ) := by exact_mod_cast hgain
      linarith
    exact (Arithmetic.patternII_impossible (c.e25 : ℚ) (c.e33 : ℚ)
      (by positivity) (by positivity) (by exact_mod_cast horder) hgainQ).elim

end Zagreb004.Profiles
