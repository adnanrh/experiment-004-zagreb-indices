import Mathlib

/-!
UNCOMPILED CANDIDATE: this session had no Lean executable.
These definitions use actual finite Mathlib simple graphs. An undirected edge
is represented by its unique ordered pair u < v, so it is counted once.
-/

set_option autoImplicit false

namespace Zagreb004

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- Explicit computable neighbor count. -/
def degree (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- Intended bridge to Mathlib's degree, not an assumed equality. -/
theorem degree_eq_mathlib (v : Fin n) : degree G v = G.degree v := by
  rw [← G.card_neighborFinset_eq_degree v, G.neighborFinset_eq_filter]
  rfl

/-- Each undirected edge is represented exactly once by its increasing pair. -/
def edges : Finset (Fin n × Fin n) :=
  (Finset.univ.product Finset.univ).filter
    (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)

def size : ℕ := (edges G).card

def firstZagreb : ℕ := ∑ v : Fin n, (degree G v) ^ 2

def secondZagreb : ℕ :=
  ∑ p ∈ edges G, degree G p.1 * degree G p.2

/-- Integer subtraction, never truncated natural-number subtraction. -/
def gap : ℤ :=
  (size G : ℤ) * (firstZagreb G : ℤ) -
    (n : ℤ) * (secondZagreb G : ℤ)

/-- Both degree endpoints must actually be attained. -/
def degreeExtrema : Prop :=
  (∀ v, 2 ≤ degree G v ∧ degree G v ≤ 5) ∧
  (∃ v, degree G v = 2) ∧ (∃ v, degree G v = 5)

def zagrebInequality : Prop :=
  (firstZagreb G : ℚ) / (n : ℚ) ≤
    (secondZagreb G : ℚ) / (size G : ℚ)

def violates : Prop :=
  (secondZagreb G : ℚ) / (size G : ℚ) <
    (firstZagreb G : ℚ) / (n : ℚ)

def counterexample : Prop :=
  G.Connected ∧ degreeExtrema G ∧ violates G

/-- An actual edge-degree count, not supplied metadata. -/
def edgeTypeCount (i j : ℕ) : ℕ :=
  ((edges G).filter (fun p =>
    min (degree G p.1) (degree G p.2) = i ∧
    max (degree G p.1) (degree G p.2) = j)).card

end Zagreb004
