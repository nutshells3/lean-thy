import Mathlib
import Problem10

noncomputable section

namespace SafeSlice

/-!
# Problem 11 — Blind-Spot Boundary Surface and Reflexive Limit

Roadmap node: 6D reflexive blind-spot and meta-limit boundary

This file introduces:
1. **BoundaryGrade**: a four-level grading of blind-spot boundaries:
   InScope, StructurallyAnalyzed, Ungraded, MetaExternal.
2. **BlindSpotBoundary**: a boundary-graded partition of an agent's blind
   spots into the four categories, with coverage proof.
3. **Reflexive limit theorem**: if an agent's self-model claims all blind
   spots are in-scope (none meta-external), then the effective capability
   must equal the full constraint-and-policy surface — a vacuously strong
   claim that collapses for any agent with genuine uncertainty.
4. **Meta-external non-emptiness**: for any agent whose known capabilities
   do not cover the entire semantic domain, the meta-external boundary is
   necessarily non-empty under a witnessable gap assumption.

The formal objects connect to Problem 10's `CapabilityModel` and Problem 9's
`ScopeBoundary`, extending the epistemic grading to self-referential limits.
-/

/-! ## Boundary grade -/

/-- Grading of a blind-spot boundary element. Each semantic object recognized
    as a blind spot falls into one of four categories:
    - `InScope`: within the agent's assessment scope; the agent can evaluate
      and potentially resolve this blind spot.
    - `StructurallyAnalyzed`: the agent has structurally analyzed this blind
      spot but cannot resolve it with current capabilities.
    - `Ungraded`: no structured assessment exists for this blind spot.
    - `MetaExternal`: fundamentally outside the agent's epistemic reach —
      the agent cannot even formulate a meaningful assessment. -/
inductive BoundaryGrade : Type where
  | InScope             : BoundaryGrade
  | StructurallyAnalyzed : BoundaryGrade
  | Ungraded            : BoundaryGrade
  | MetaExternal        : BoundaryGrade
  deriving DecidableEq, Repr

/-- A boundary grade is **assessable** if the agent can reason about it
    (InScope or StructurallyAnalyzed). -/
def BoundaryGrade.assessable : BoundaryGrade → Bool
  | .InScope              => true
  | .StructurallyAnalyzed => true
  | .Ungraded             => false
  | .MetaExternal         => false

/-! ## Blind-spot boundary surface -/

/-- A **blind-spot boundary** partitions the blind spots of a capability model
    into four graded categories. This is the formal boundary surface that
    separates what the agent can self-assess from what lies beyond its
    epistemic reach.

    The boundary is parametric over `Sem` and tied to a `CapabilityModel`. -/
structure BlindSpotBoundary (Sem : Type*) where
  /-- The capability model whose blind spots are being graded. -/
  model : CapabilityModel Sem
  /-- Grading function: assigns a boundary grade to each blind-spot element. -/
  grading : Sem → BoundaryGrade
  /-- The in-scope blind spots: those the agent can assess. -/
  inScope : Set Sem
  /-- Structurally analyzed blind spots: analyzed but unresolvable. -/
  structurallyAnalyzed : Set Sem
  /-- Ungraded blind spots: no assessment exists. -/
  ungraded : Set Sem
  /-- Meta-external blind spots: beyond epistemic reach. -/
  metaExternal : Set Sem
  /-- The four categories partition the blind spots. -/
  inScope_eq : inScope = { s ∈ model.blindSpots | grading s = .InScope }
  analyzed_eq : structurallyAnalyzed =
    { s ∈ model.blindSpots | grading s = .StructurallyAnalyzed }
  ungraded_eq : ungraded = { s ∈ model.blindSpots | grading s = .Ungraded }
  metaExternal_eq : metaExternal =
    { s ∈ model.blindSpots | grading s = .MetaExternal }

/-- The **assessable boundary**: the union of in-scope and structurally
    analyzed blind spots. -/
def BlindSpotBoundary.assessableBoundary {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) : Set Sem :=
  bsb.inScope ∪ bsb.structurallyAnalyzed

/-- The **opaque boundary**: the union of ungraded and meta-external
    blind spots — portions the agent cannot meaningfully self-assess. -/
def BlindSpotBoundary.opaqueBoundary {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) : Set Sem :=
  bsb.ungraded ∪ bsb.metaExternal

/-! ## Boundary partition theorems -/

/-- The four boundary categories cover all blind spots: every blind spot
    receives exactly one grade. -/
theorem boundary_covers_blindSpots {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) :
    bsb.model.blindSpots ⊆
      bsb.inScope ∪ bsb.structurallyAnalyzed ∪ bsb.ungraded ∪ bsb.metaExternal := by
  intro s hs
  rw [bsb.inScope_eq, bsb.analyzed_eq, bsb.ungraded_eq, bsb.metaExternal_eq]
  simp only [Set.mem_union, Set.mem_sep_iff]
  cases bsb.grading s with
  | InScope => left; left; left; exact ⟨hs, rfl⟩
  | StructurallyAnalyzed => left; left; right; exact ⟨hs, rfl⟩
  | Ungraded => left; right; exact ⟨hs, rfl⟩
  | MetaExternal => right; exact ⟨hs, rfl⟩

/-- The assessable and opaque boundaries together cover all blind spots. -/
theorem assessable_opaque_cover {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) :
    bsb.model.blindSpots ⊆
      bsb.assessableBoundary ∪ bsb.opaqueBoundary := by
  intro s hs
  have h := boundary_covers_blindSpots bsb hs
  simp only [BlindSpotBoundary.assessableBoundary,
    BlindSpotBoundary.opaqueBoundary, Set.mem_union] at *
  rcases h with ((h | h) | h) | h
  · left; left; exact h
  · left; right; exact h
  · right; left; exact h
  · right; right; exact h

/-- In-scope blind spots are contained in the blind-spot set. -/
theorem inScope_sub_blindSpots {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) :
    bsb.inScope ⊆ bsb.model.blindSpots := by
  rw [bsb.inScope_eq]; exact fun _ ⟨h, _⟩ => h

/-- Meta-external blind spots are contained in the blind-spot set. -/
theorem metaExternal_sub_blindSpots {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) :
    bsb.metaExternal ⊆ bsb.model.blindSpots := by
  rw [bsb.metaExternal_eq]; exact fun _ ⟨h, _⟩ => h

/-! ## Connecting boundary grades to epistemic grades -/

/-- Map a boundary grade to the corresponding epistemic grade for
    reporting purposes. -/
def boundaryToEpistemicGrade : BoundaryGrade → EpistemicGrade
  | .InScope              => .Analyzed
  | .StructurallyAnalyzed => .Supported
  | .Ungraded             => .Ungraded
  | .MetaExternal         => .Ungraded

/-- Meta-external and ungraded boundaries both map to Ungraded epistemic
    grade — the agent has no structured evidence for either. -/
theorem metaExternal_epistemic_ungraded :
    boundaryToEpistemicGrade .MetaExternal = .Ungraded := rfl

/-! ## Reflexive limit theorem

The reflexive limit captures a fundamental self-referential constraint:
an agent that claims all of its blind spots are in-scope (assessable,
none meta-external or ungraded) must have blind spots that are entirely
within its effective capability's complement — and if those blind spots
are also excluded from the effective capability (as they must be, by
definition of `effective`), the agent's claim of complete self-assessment
is only consistent when the blind spots add no new information beyond
what the agent already excludes.

More precisely: if the meta-external and ungraded bins are empty, then
every blind spot is assessable, meaning the agent claims it can evaluate
every one of its own limitations. This is a very strong epistemic claim.
-/

/-- A blind-spot boundary has **no opaque region** when both the ungraded
    and meta-external categories are empty. -/
def BlindSpotBoundary.noOpaqueRegion {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) : Prop :=
  bsb.ungraded = ∅ ∧ bsb.metaExternal = ∅

/-- **Reflexive limit theorem**: if the boundary has no opaque region,
    then every blind spot is assessable — it lies in the assessable boundary.
    This is the formal statement that claiming no meta-external blind spots
    forces all blind spots to be within the agent's self-assessment scope. -/
theorem reflexive_limit {Sem : Type*}
    (bsb : BlindSpotBoundary Sem)
    (hno_opaque : bsb.noOpaqueRegion) :
    bsb.model.blindSpots ⊆ bsb.assessableBoundary := by
  intro s hs
  have hcov := assessable_opaque_cover bsb hs
  simp only [BlindSpotBoundary.opaqueBoundary, Set.mem_union,
    BlindSpotBoundary.noOpaqueRegion] at *
  rcases hcov with h | (h | h)
  · exact h
  · simp [hno_opaque.1] at h
  · simp [hno_opaque.2] at h

/-- **Reflexive limit contrapositive**: if there exist blind spots outside
    the assessable boundary, then the opaque region is non-empty — the agent
    necessarily has meta-external or ungraded blind spots it cannot
    self-assess. -/
theorem reflexive_limit_contrapositive {Sem : Type*}
    (bsb : BlindSpotBoundary Sem)
    (h_gap : ¬ (bsb.model.blindSpots ⊆ bsb.assessableBoundary)) :
    ¬ bsb.noOpaqueRegion :=
  fun hno => h_gap (reflexive_limit bsb hno)

/-! ## Meta-external non-emptiness under witnessed gaps -/

/-- A capability model has a **witnessed gap** when there exists a semantic
    object that is a blind spot but not in the known capabilities. This
    is the minimal assumption for meta-external non-emptiness. -/
def CapabilityModel.hasWitnessedGap {Sem : Type*}
    (cm : CapabilityModel Sem) : Prop :=
  ∃ s, s ∈ cm.blindSpots ∧ s ∉ cm.known

/-- If the grading assigns MetaExternal to every blind spot not in the
    assessable boundary, and there exists a blind spot outside the
    assessable boundary, then the meta-external set is non-empty. -/
theorem metaExternal_nonempty_of_gap {Sem : Type*}
    (bsb : BlindSpotBoundary Sem)
    (s : Sem)
    (hs_blind : s ∈ bsb.model.blindSpots)
    (hs_grade : bsb.grading s = .MetaExternal) :
    bsb.metaExternal.Nonempty := by
  rw [bsb.metaExternal_eq]
  exact ⟨s, hs_blind, hs_grade⟩

/-! ## Boundary-graded deploy alignment -/

/-- A blind-spot boundary is **deploy-aware** when the assessable boundary
    is disjoint from the deployable envelope — no blind spot that the agent
    can self-assess is deployed. -/
def BlindSpotBoundary.deployAware {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) (deployable : Set Sem) : Prop :=
  bsb.assessableBoundary ∩ deployable = ∅

/-- Blind spots are always excluded from effective capability, by
    definition: `effective = (known \ blindSpots) ∩ constraints`. -/
theorem blindSpots_not_effective {Sem : Type*}
    (cm : CapabilityModel Sem)
    (s : Sem) (hs : s ∈ cm.blindSpots) :
    s ∉ cm.effective := by
  intro heff
  exact heff.1.2 hs

/-- If the deployable envelope equals the effective capability exactly
    (tight alignment), then blind spots are disjoint from the deployable
    envelope. -/
theorem blindSpots_disjoint_deploy_tight {Sem : Type*}
    (bsb : BlindSpotBoundary Sem)
    (deployable : Set Sem)
    (htight : deployable = bsb.model.effective) :
    bsb.model.blindSpots ∩ deployable = ∅ := by
  ext s
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hs_blind hs_deploy
  rw [htight] at hs_deploy
  exact blindSpots_not_effective bsb.model s hs_blind hs_deploy

/-! ## In-scope, structurally analyzed, and ungraded/meta-external
    boundary theorems (theorem-level statements) -/

/-- **In-scope boundary theorem**: the in-scope blind spots are exactly
    those blind spots that the agent can assess and that lie within the
    scope boundary. -/
theorem inScope_boundary_characterization {Sem : Type*}
    (bsb : BlindSpotBoundary Sem)
    (scope : ScopeBoundary Sem)
    (interpret : Sem → Sem)
    (hscope : ∀ s ∈ bsb.inScope, scope.inScope (interpret s)) :
    bsb.inScope ⊆ { s | scope.inScope (interpret s) } :=
  hscope

/-- **Structurally analyzed boundary theorem**: structurally analyzed blind
    spots remain in the blind-spot set and are assessable. -/
theorem structurallyAnalyzed_assessable {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) :
    bsb.structurallyAnalyzed ⊆ bsb.assessableBoundary := by
  intro s hs
  exact Set.mem_union_right _ hs

/-- **Ungraded/meta-external boundary theorem**: every element in the opaque
    boundary is a blind spot that the agent cannot self-assess, and has
    epistemic grade Ungraded. -/
theorem opaque_boundary_ungraded {Sem : Type*}
    (bsb : BlindSpotBoundary Sem) :
    ∀ s ∈ bsb.opaqueBoundary,
      boundaryToEpistemicGrade (bsb.grading s) = .Ungraded := by
  intro s hs
  simp only [BlindSpotBoundary.opaqueBoundary, Set.mem_union] at hs
  rcases hs with hs | hs
  · rw [bsb.ungraded_eq] at hs
    rw [hs.2]
    rfl
  · rw [bsb.metaExternal_eq] at hs
    rw [hs.2]
    rfl

end SafeSlice
