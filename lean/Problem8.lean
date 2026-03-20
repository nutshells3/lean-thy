import Mathlib
import Problem7

noncomputable section

namespace SafeSlice

/-!
# Problem 8 — Epistemic Grade Calculus

Roadmap node: 6A structured epistemic grade calculus

This file introduces a typed epistemic-grade system that replaces prose
Track A/B/C labels with formal grade objects. The key components are:

1. `EpistemicGrade` — an ordered inductive with four levels.
2. `GradedClaim` — a claim carrying a grade, optional subclaim tree, and
   evidential-trajectory (slope) metadata.
3. Recursive aggregation: the grade of a composite claim is the minimum
   grade of its subclaims.
4. `Slope` — evidential trajectory metadata at theorem level, tracking
   whether a claim's grade is improving, stable, or degrading.
5. Report carriers that later orchestration nodes can reuse.

Forbidden shortcut: source identity is *not* baked into the grade
definition; grades are purely evidential.
-/

/-! ## Core grade type -/

/-- The four epistemic grades, ordered from strongest to weakest.
    - `Proven`: machine-checked formal proof exists.
    - `Supported`: substantial formal or semi-formal evidence, not yet
      fully machine-checked.
    - `Analyzed`: systematic analysis exists but no proof attempt.
    - `Ungraded`: no structured evidence. -/
inductive EpistemicGrade : Type where
  | Proven    : EpistemicGrade
  | Supported : EpistemicGrade
  | Analyzed  : EpistemicGrade
  | Ungraded  : EpistemicGrade
  deriving DecidableEq, Repr

namespace EpistemicGrade

/-- Numeric rank for ordering: lower is stronger. -/
def rank : EpistemicGrade → ℕ
  | Proven    => 0
  | Supported => 1
  | Analyzed  => 2
  | Ungraded  => 3

/-- The grade ordering: g₁ ≤ g₂ iff g₁ is at least as strong as g₂
    (i.e. lower rank). -/
instance : LE EpistemicGrade where
  le g₁ g₂ := g₁.rank ≤ g₂.rank

instance : DecidableRel (α := EpistemicGrade) (· ≤ ·) :=
  fun a b => Nat.decLe a.rank b.rank

theorem le_refl (g : EpistemicGrade) : g ≤ g := Nat.le_refl _

theorem le_trans {a b c : EpistemicGrade} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    a ≤ c := Nat.le_trans h₁ h₂

theorem le_antisymm {a b : EpistemicGrade} (h₁ : a ≤ b) (h₂ : b ≤ a) :
    a = b := by
  have h := Nat.le_antisymm h₁ h₂
  cases a <;> cases b <;> simp_all [rank]

theorem le_total (a b : EpistemicGrade) : a ≤ b ∨ b ≤ a := by
  change a.rank ≤ b.rank ∨ b.rank ≤ a.rank
  exact Nat.le_total a.rank b.rank

/-- Proven is the strongest grade. -/
theorem proven_le (g : EpistemicGrade) : Proven ≤ g := Nat.zero_le _

/-- Ungraded is the weakest grade. -/
theorem le_ungraded (g : EpistemicGrade) : g ≤ Ungraded := by
  cases g <;> decide

/-- Minimum of two grades (strongest = lowest rank). -/
def min (a b : EpistemicGrade) : EpistemicGrade :=
  if a ≤ b then a else b

/-- Maximum of two grades (weakest = highest rank). -/
def max (a b : EpistemicGrade) : EpistemicGrade :=
  if a ≤ b then b else a

theorem le_max_left (a b : EpistemicGrade) : a ≤ max a b := by
  simp only [max]
  split
  · assumption
  · exact le_refl a

theorem le_max_right (a b : EpistemicGrade) : b ≤ max a b := by
  simp only [max]
  split
  · exact le_refl b
  · rename_i h
    have := le_total a b
    rcases this with h' | h'
    · exact absurd h' h
    · exact h'

end EpistemicGrade

/-! ## Slope: evidential trajectory metadata -/

/-- Evidential trajectory of a claim's grade over time or across
    formalization cycles.
    - `Improving`: grade has strengthened since last assessment.
    - `Stable`: grade unchanged.
    - `Degrading`: grade has weakened (e.g., a dependency was retracted). -/
inductive Slope : Type where
  | Improving : Slope
  | Stable    : Slope
  | Degrading : Slope
  deriving DecidableEq, Repr, BEq

/-! ## Graded claims and recursive decomposition -/

/-- A **graded claim** over a semantic type `Sem`. Each claim carries:
    - `label`: a human-readable identifier for the claim.
    - `grade`: its epistemic grade.
    - `slope`: evidential trajectory metadata.
    - `subclaims`: a list of graded subclaims supporting this claim.
      Recursive decomposition is captured by this tree structure. -/
inductive GradedClaim (Sem : Type*) : Type _ where
  | mk (label : String) (grade : EpistemicGrade) (slope : Slope)
       (subclaims : List (GradedClaim Sem)) : GradedClaim Sem

namespace GradedClaim

variable {Sem : Type*}

/-- Extract the label of a graded claim. -/
def label : GradedClaim Sem → String
  | mk l _ _ _ => l

/-- Extract the grade of a graded claim. -/
def grade : GradedClaim Sem → EpistemicGrade
  | mk _ g _ _ => g

/-- Extract the slope of a graded claim. -/
def slope : GradedClaim Sem → Slope
  | mk _ _ s _ => s

/-- Extract the subclaims of a graded claim. -/
def subclaims : GradedClaim Sem → List (GradedClaim Sem)
  | mk _ _ _ cs => cs

/-- A claim is a **leaf** if it has no subclaims. -/
def isLeaf (c : GradedClaim Sem) : Prop := c.subclaims = []

instance (c : GradedClaim Sem) : Decidable c.isLeaf :=
  inferInstanceAs (Decidable (c.subclaims = []))

/-! ### Recursive aggregation -/

/-- The weakest grade in a list of graded claims, starting from an
    accumulator. This avoids termination issues with nested foldl. -/
def weakestGrade : List (GradedClaim Sem) → EpistemicGrade → EpistemicGrade
  | [], acc => acc
  | c :: cs, acc => weakestGrade cs (EpistemicGrade.max acc c.grade)

/-- Aggregate grade of a claim tree: the weakest (highest-rank) grade
    among the claim and its immediate subclaims.
    This formalizes the rule that a composite claim is only as strong
    as its weakest component. -/
def aggregateGrade (c : GradedClaim Sem) : EpistemicGrade :=
  weakestGrade c.subclaims c.grade

/-- For a leaf claim, the aggregate grade equals the claim's own grade. -/
theorem aggregateGrade_leaf (l : String) (g : EpistemicGrade) (s : Slope) :
    (GradedClaim.mk l g s ([] : List (GradedClaim Sem))).aggregateGrade = g := rfl

/-- The aggregate grade is at least as weak as the claim's own grade. -/
theorem grade_le_weakestGrade (cs : List (GradedClaim Sem)) (acc : EpistemicGrade) :
    acc ≤ weakestGrade cs acc := by
  induction cs generalizing acc with
  | nil => exact EpistemicGrade.le_refl acc
  | cons c cs ih =>
    simp only [weakestGrade]
    exact EpistemicGrade.le_trans (EpistemicGrade.le_max_left acc c.grade) (ih _)

theorem grade_le_aggregateGrade (c : GradedClaim Sem) :
    c.grade ≤ c.aggregateGrade := by
  simp only [aggregateGrade]
  exact grade_le_weakestGrade c.subclaims c.grade

/-! ### Deep recursive aggregation -/

/-- Deep aggregate: the weakest grade across the **entire** claim tree,
    recursing into all subclaim levels. Unlike `aggregateGrade` which
    considers only immediate subclaims, this traverses the full tree. -/
def deepAggregateGrade (c : GradedClaim Sem) : EpistemicGrade :=
  match c with
  | mk _ g _ cs => cs.foldl (fun acc sub => EpistemicGrade.max acc (deepAggregateGrade sub)) g
termination_by sizeOf c

/-- For a leaf, deep aggregate equals the claim's own grade. -/
theorem deepAggregateGrade_leaf (l : String) (g : EpistemicGrade) (s : Slope) :
    (GradedClaim.mk l g s ([] : List (GradedClaim Sem))).deepAggregateGrade = g := by
  simp [deepAggregateGrade]

end GradedClaim

/-! ## Well-formedness invariants -/

/-- A graded-claim tree is **grade-consistent** when every node's grade
    is at least as weak as (≥) the grade of each subclaim. That is, you
    cannot claim `Proven` if a subclaim is only `Analyzed`. -/
def GradedClaim.gradeConsistent {Sem : Type*} : GradedClaim Sem → Prop
  | .mk _ g _ cs =>
    (∀ c ∈ cs, g ≤ c.grade) ∧
    (∀ c ∈ cs, c.gradeConsistent)

/-! ## Report carriers -/

/-- A **theory-level report** summarizes the epistemic status of a
    collection of graded claims, suitable for consumption by orchestration
    or planning layers. -/
structure TheoryReport (Sem : Type*) where
  /-- The claims in this report. -/
  claims : List (GradedClaim Sem)
  /-- Overall grade: the weakest grade among all claims. -/
  overallGrade : EpistemicGrade
  /-- Overall slope: Degrading if any claim is degrading, else Improving
      if any is improving, else Stable. -/
  overallSlope : Slope
  /-- Number of claims at each grade level. -/
  gradeCounts : EpistemicGrade → ℕ

/-- Construct a theory report from a list of claims. -/
def TheoryReport.fromClaims {Sem : Type*}
    (claims : List (GradedClaim Sem)) : TheoryReport Sem where
  claims := claims
  overallGrade := claims.foldl
    (fun acc c => EpistemicGrade.max acc c.grade) .Proven
  overallSlope :=
    if claims.any (fun c => c.slope == .Degrading) then .Degrading
    else if claims.any (fun c => c.slope == .Improving) then .Improving
    else .Stable
  gradeCounts := fun g =>
    (claims.filter (fun c => c.grade == g)).length

/-- A **capability-level report** ties a theory report to a specific
    proposer and regime, enabling orchestration to reason about the
    epistemic quality of a role's coverage. -/
structure CapabilityReport (Sem : Type*) where
  /-- The proposer whose coverage is being graded. -/
  proposer : Proposer Sem
  /-- The admissibility regime. -/
  regime : AdmRegime Sem
  /-- The epistemic report for claims within Deploy(G, M). -/
  report : TheoryReport Sem

/-- A capability report is **deploy-scoped** when every claim in the
    report targets a semantic object in Deploy(G, M). -/
def CapabilityReport.deployScoped {Sem : Type*}
    (cr : CapabilityReport Sem) (targets : GradedClaim Sem → Sem) : Prop :=
  ∀ c ∈ cr.report.claims, targets c ∈ Deploy cr.proposer cr.regime

/-! ## Connecting grades to orchestration -/

/-- A role placement is **grade-aware** when every task's target has a
    graded claim at or above a specified minimum grade threshold. -/
def RolePlacement.gradeAware {Sem : Type*}
    (rp : RolePlacement Sem)
    (grading : Sem → EpistemicGrade)
    (minGrade : EpistemicGrade) : Prop :=
  ∀ t ∈ rp.plan.tasks, grading t.target ≤ minGrade

end SafeSlice
