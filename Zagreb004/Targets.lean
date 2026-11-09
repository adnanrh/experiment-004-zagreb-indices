import Zagreb004.Definitions
import Zagreb004.Profiles

/-!
UNCOMPILED CANDIDATE.
These are specifications (definitions of propositions), NOT proof declarations.
In particular, defining `MinimalityTarget` does not prove minimality.
-/
set_option autoImplicit false

namespace Zagreb004

def Exists46Target : Prop :=
  ∃ G : SimpleGraph (Fin 46),
    ∃ d : DecidableRel G.Adj, @counterexample 46 G d

def MinimalityTarget : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (d : DecidableRel G.Adj),
    n ≤ 45 → G.Connected → @degreeExtrema n G d →
    @zagrebInequality n G d

def AllOrdersTarget : Prop :=
  ∀ n : ℕ, 46 ≤ n →
    ∃ G : SimpleGraph (Fin n),
      ∃ d : DecidableRel G.Adj, @counterexample n G d

/-- Extract the ten counts from a graph rather than assume their values. -/
def graphProfile {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Profiles.Counts where
  e22 := edgeTypeCount G 2 2
  e23 := edgeTypeCount G 2 3
  e24 := edgeTypeCount G 2 4
  e25 := edgeTypeCount G 2 5
  e33 := edgeTypeCount G 3 3
  e34 := edgeTypeCount G 3 4
  e35 := edgeTypeCount G 3 5
  e44 := edgeTypeCount G 4 4
  e45 := edgeTypeCount G 4 5
  e55 := edgeTypeCount G 5 5

def ExtremalProfileTarget : Prop :=
  ∀ (G : SimpleGraph (Fin 46)) (d : DecidableRel G.Adj),
    @counterexample 46 G d → @graphProfile 46 G d = Profiles.canonical

def FullTarget : Prop :=
  Exists46Target ∧ MinimalityTarget ∧ AllOrdersTarget ∧ ExtremalProfileTarget

end Zagreb004
