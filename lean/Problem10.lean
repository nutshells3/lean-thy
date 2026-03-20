import Mathlib
import Problem9

noncomputable section

namespace SafeSlice

/-!
# Problem 10 — Graded Capability Model and Feasibility Reports

Roadmap node: 6C graded capability model and feasibility reports

This file introduces:
1. **CapabilityModel**: a self-model carrying the agent's known capabilities,
   operational constraints, failure history, and recognized blind spots.
2. **FeasibilityStatus**: a decidable three-valued judgment (Feasible,
   Infeasible, Uncertain) for each step in a multi-step plan.
3. **FeasibilityReport**: a per-step feasibility grading for a task plan,
   with blockers, fallback paths, and risk annotations.
4. **Infeasibility-filtering theorem**: proven-infeasible steps are filtered
   pre-execution; feasible and uncertain steps pass through with explicit
   grading.
5. Connection to the Track system from Problem 9 and orchestration objects
   from Problem 7.

The formal objects mirror the shape of the `safe_slice` detector/report
artifact: the detector partitions steps into safe (feasible), unsafe
(infeasible), and uncertain bins, with blocker annotations.
-/

/-! ## Capability model -/

/-- A **capability model** is the agent's self-assessment of what it can
    handle within a semantic domain `Sem`. It carries:
    - `known`: semantic objects the agent believes it can handle.
    - `constraints`: operational constraints (subset of `Sem` the agent
      is allowed to attempt).
    - `failureHistory`: semantics that have previously failed.
    - `blindSpots`: semantics the agent recognizes it cannot assess.

    The model is parametric over `Sem` to align with `Deploy(G, M)`. -/
structure CapabilityModel (Sem : Type*) where
  /-- Semantic objects the agent believes it can handle. -/
  known : Set Sem
  /-- Operational constraints: the subset the agent is allowed to attempt. -/
  constraints : Set Sem
  /-- Previously failed semantic objects. -/
  failureHistory : Set Sem
  /-- Semantic objects the agent recognizes it cannot assess. -/
  blindSpots : Set Sem

/-- The **effective capability** of a model: known capabilities minus
    blind spots, intersected with operational constraints. -/
def CapabilityModel.effective {Sem : Type*} (cm : CapabilityModel Sem) : Set Sem :=
  (cm.known \ cm.blindSpots) ∩ cm.constraints

/-- A capability model is **conservative** when the effective capability
    excludes the failure history. -/
def CapabilityModel.conservative {Sem : Type*} (cm : CapabilityModel Sem) : Prop :=
  cm.effective ∩ cm.failureHistory = ∅

/-- A capability model is **deploy-aligned** when the effective capability
    is contained in a given deployable envelope. -/
def CapabilityModel.deployAligned {Sem : Type*}
    (cm : CapabilityModel Sem) (deployable : Set Sem) : Prop :=
  cm.effective ⊆ deployable

/-! ## Feasibility status -/

/-- Three-valued feasibility judgment for a plan step.
    - `Feasible`: the step is within effective capability and passes
      all regime checks.
    - `Infeasible`: the step is provably outside effective capability
      or blocked by a known constraint.
    - `Uncertain`: the step cannot be classified; it may lie in a blind
      spot or lack sufficient evidence. -/
inductive FeasibilityStatus : Type where
  | Feasible   : FeasibilityStatus
  | Infeasible : FeasibilityStatus
  | Uncertain  : FeasibilityStatus
  deriving DecidableEq, Repr, BEq

/-- A feasibility status is **passable** (not proven-infeasible). -/
def FeasibilityStatus.passable : FeasibilityStatus → Bool
  | .Feasible   => true
  | .Infeasible => false
  | .Uncertain  => true

/-! ## Step feasibility with blockers -/

/-- A **blocker** explains why a step is infeasible or uncertain. -/
structure Blocker where
  /-- Blocker category identifier. -/
  category : String
  /-- Human-readable description. -/
  description : String
  deriving DecidableEq, Repr

/-- A **fallback path** for an infeasible or uncertain step. -/
structure FallbackPath (Sem : Type*) where
  /-- The alternative semantic target. -/
  target : Sem
  /-- Description of the fallback. -/
  description : String

/-- A **step feasibility** record: the feasibility judgment for one step,
    with blockers, fallback paths, and a risk annotation.
    This mirrors the detector/report artifact shape. -/
structure StepFeasibility (Sem : Type*) where
  /-- The task being assessed. -/
  task : Task Sem
  /-- The feasibility judgment. -/
  status : FeasibilityStatus
  /-- Blockers explaining infeasibility or uncertainty. -/
  blockers : List Blocker
  /-- Fallback paths (if any). -/
  fallbacks : List (FallbackPath Sem)
  /-- Risk annotation: the risk measure of the task target under the
      assessing role's regime. -/
  riskAnnotation : NNReal
  /-- Epistemic grade of the step's assessment. -/
  grade : EpistemicGrade

/-! ## Feasibility report -/

/-- A **feasibility report** grades every step in a task plan with a
    feasibility status, blockers, fallbacks, and risk annotations.
    This is the pre-execution grading object that orchestration uses to
    filter infeasible steps before committing resources. -/
structure FeasibilityReport (Sem : Type*) where
  /-- The underlying task plan. -/
  plan : TaskPlan Sem
  /-- The capability model used for assessment. -/
  capabilityModel : CapabilityModel Sem
  /-- The role performing the assessment. -/
  assessingRole : Role Sem
  /-- Per-step feasibility assessments. -/
  assessments : List (StepFeasibility Sem)
  /-- Every assessed task is from the plan. -/
  assessments_cover : ∀ sf ∈ assessments, sf.task ∈ plan.tasks

/-- The **infeasible steps** of a feasibility report. -/
def FeasibilityReport.infeasibleSteps {Sem : Type*}
    (fr : FeasibilityReport Sem) : List (StepFeasibility Sem) :=
  fr.assessments.filter (fun sf => sf.status == .Infeasible)

/-- The **passable steps** of a feasibility report (feasible or uncertain). -/
def FeasibilityReport.passableSteps {Sem : Type*}
    (fr : FeasibilityReport Sem) : List (StepFeasibility Sem) :=
  fr.assessments.filter (fun sf => sf.status.passable)

/-- The **uncertain steps** of a feasibility report. -/
def FeasibilityReport.uncertainSteps {Sem : Type*}
    (fr : FeasibilityReport Sem) : List (StepFeasibility Sem) :=
  fr.assessments.filter (fun sf => sf.status == .Uncertain)

/-! ## Infeasibility-filtering theorem -/

/-- A feasibility report is **well-classified** when:
    - Infeasible steps have at least one blocker.
    - Feasible steps have the task target in the capability model's
      effective capability. -/
def FeasibilityReport.wellClassified {Sem : Type*}
    (fr : FeasibilityReport Sem) : Prop :=
  (∀ sf ∈ fr.assessments, sf.status = .Infeasible → sf.blockers ≠ []) ∧
  (∀ sf ∈ fr.assessments, sf.status = .Feasible →
    sf.task.target ∈ fr.capabilityModel.effective)

/-- **Infeasibility-filtering theorem**: in a well-classified report,
    every passable step has its target in the capability model's effective
    capability or is explicitly marked uncertain. Equivalently, no
    infeasible step passes the filter. -/
theorem infeasibility_filter_sound {Sem : Type*}
    (fr : FeasibilityReport Sem)
    (_hwc : fr.wellClassified) :
    ∀ sf ∈ fr.passableSteps,
      sf.status = .Feasible ∨ sf.status = .Uncertain := by
  intro sf hsf
  simp only [FeasibilityReport.passableSteps, List.mem_filter] at hsf
  obtain ⟨_, hpass⟩ := hsf
  have hp := hpass
  revert hp
  cases sf.status <;> simp [FeasibilityStatus.passable]

/-- **No infeasible step passes**: the passable filter excludes every
    infeasible step. -/
theorem no_infeasible_passes {Sem : Type*}
    (fr : FeasibilityReport Sem) :
    ∀ sf ∈ fr.passableSteps, sf.status ≠ .Infeasible := by
  intro sf hsf habs
  simp only [FeasibilityReport.passableSteps, List.mem_filter] at hsf
  obtain ⟨_, hpass⟩ := hsf
  revert hpass
  rw [habs]
  simp [FeasibilityStatus.passable]

/-- **Infeasible steps have blockers**: in a well-classified report,
    every infeasible step carries at least one blocker. -/
theorem infeasible_has_blockers {Sem : Type*}
    (fr : FeasibilityReport Sem)
    (hwc : fr.wellClassified) :
    ∀ sf ∈ fr.infeasibleSteps, sf.blockers ≠ [] := by
  intro sf hsf
  simp only [FeasibilityReport.infeasibleSteps, List.mem_filter] at hsf
  rcases hsf with ⟨hmem, hstatus⟩
  have hbeq : sf.status = .Infeasible := by
    revert hstatus; cases sf.status <;> decide
  exact hwc.1 sf hmem hbeq

/-- **Feasible steps are in effective capability**: in a well-classified
    report, every feasible step's target is in the capability model's
    effective set. -/
theorem feasible_in_effective {Sem : Type*}
    (fr : FeasibilityReport Sem)
    (hwc : fr.wellClassified) :
    ∀ sf ∈ fr.assessments, sf.status = .Feasible →
      sf.task.target ∈ fr.capabilityModel.effective :=
  hwc.2

/-! ## Connecting feasibility to tracks -/

/-- The **epistemic track** of a step assessment is determined by its
    grade, using the source-agnostic routing from Problem 9. -/
def StepFeasibility.track {Sem : Type*} (sf : StepFeasibility Sem) : Track :=
  gradeToTrack sf.grade

/-- Feasible steps at Track A grade have machine-checked evidence. -/
theorem feasible_trackA_proven {Sem : Type*}
    (sf : StepFeasibility Sem)
    (_hfeas : sf.status = .Feasible)
    (htrack : sf.track = .A) :
    sf.grade = .Proven := by
  revert htrack
  cases h : sf.grade <;> simp_all [StepFeasibility.track, gradeToTrack]

/-! ## Connecting feasibility to deployment -/

/-- A feasibility report is **deploy-consistent** when every feasible
    step's target lies in `Deploy(G, M)` for the assessing role. -/
def FeasibilityReport.deployConsistent {Sem : Type*}
    (fr : FeasibilityReport Sem) : Prop :=
  ∀ sf ∈ fr.assessments, sf.status = .Feasible →
    sf.task.target ∈ Deploy fr.assessingRole.proposer fr.assessingRole.regime

/-- **Deploy-consistency from alignment**: if the capability model is
    deploy-aligned with the assessing role's deployable envelope, and the
    report is well-classified, then the report is deploy-consistent. -/
theorem deployConsistent_of_aligned {Sem : Type*}
    (fr : FeasibilityReport Sem)
    (hwc : fr.wellClassified)
    (halign : fr.capabilityModel.deployAligned
      (Deploy fr.assessingRole.proposer fr.assessingRole.regime)) :
    fr.deployConsistent := by
  intro sf hmem hfeas
  exact halign (hwc.2 sf hmem hfeas)

/-! ## Partition completeness -/

/-- Every assessment falls into exactly one of the three bins. -/
theorem feasibility_partition_complete {Sem : Type*}
    (fr : FeasibilityReport Sem) :
    ∀ sf ∈ fr.assessments,
      sf.status = .Feasible ∨
      sf.status = .Infeasible ∨
      sf.status = .Uncertain := by
  intro sf _
  cases sf.status with
  | Feasible => left; rfl
  | Infeasible => right; left; rfl
  | Uncertain => right; right; rfl

/-- The passable and infeasible steps together cover all assessments. -/
theorem passable_infeasible_cover {Sem : Type*}
    (fr : FeasibilityReport Sem) :
    ∀ sf ∈ fr.assessments,
      sf ∈ fr.passableSteps ∨ sf ∈ fr.infeasibleSteps := by
  intro sf hmem
  simp only [FeasibilityReport.passableSteps, FeasibilityReport.infeasibleSteps,
    List.mem_filter, FeasibilityStatus.passable]
  cases sf.status with
  | Feasible => left; exact ⟨hmem, rfl⟩
  | Infeasible => right; exact ⟨hmem, rfl⟩
  | Uncertain => left; exact ⟨hmem, rfl⟩

end SafeSlice
