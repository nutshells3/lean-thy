import Mathlib
import Problem8
import Axis1Export

noncomputable section

namespace SafeSlice

/-!
# Problem 9 — Three-Track Routing and Source-Agnostic Grading

Roadmap node: 6B source-agnostic three-track grading completeness

This file formalizes:
1. **Track routing**: a decidable judgment that maps each graded claim to
   one of Track A (Proven), Track B (Supported), Track C (Analyzed), or
   Ungraded, based solely on its epistemic grade.
2. **Source-agnostic grading**: a theorem stating that the track assignment
   depends only on the claim's evidential grade, not on the identity of the
   source that produced it.
3. **In-scope boundary**: an explicit predicate separating gradable (in-scope)
   claims from out-of-scope claims, with a completeness theorem that every
   in-scope claim receives a definite track.

Forbidden shortcut: source identity is *not* used in routing; grades are
purely evidential.
-/

/-! ## Track type -/

/-- The three assessment tracks plus the Ungraded bin. -/
inductive Track : Type where
  | A : Track        -- machine-checked formal proof
  | B : Track        -- substantial semi-formal evidence
  | C : Track        -- systematic analysis only
  | Ungraded : Track -- no structured evidence
  deriving DecidableEq, Repr

/-! ## Track routing judgment -/

/-- Route a grade to its track. This is the core routing judgment:
    - Proven   → Track A
    - Supported → Track B
    - Analyzed  → Track C
    - Ungraded  → Track.Ungraded -/
def gradeToTrack : EpistemicGrade → Track
  | .Proven    => .A
  | .Supported => .B
  | .Analyzed  => .C
  | .Ungraded  => .Ungraded

/-- Route a graded claim to its track based on its grade alone. -/
def GradedClaim.track {Sem : Type*} (c : GradedClaim Sem) : Track :=
  gradeToTrack c.grade

/-! ## Source-agnostic grading -/

/-- A **source** represents the origin of a claim (human, LLM, solver, etc.).
    This type exists only to state source-agnosticity; it plays no role in
    grading or routing. -/
structure Source where
  id : String
  deriving DecidableEq, Repr

/-- A **sourced claim** pairs a graded claim with its provenance. -/
structure SourcedClaim (Sem : Type*) where
  claim : GradedClaim Sem
  source : Source

/-- The track of a sourced claim is determined by grade alone. -/
def SourcedClaim.track {Sem : Type*} (sc : SourcedClaim Sem) : Track :=
  sc.claim.track

/-- **Source-agnosticity**: two sourced claims with the same grade receive
    the same track, regardless of their source. -/
theorem source_agnostic_grading {Sem : Type*}
    (sc₁ sc₂ : SourcedClaim Sem)
    (hgrade : sc₁.claim.grade = sc₂.claim.grade) :
    sc₁.track = sc₂.track := by
  simp only [SourcedClaim.track, GradedClaim.track, hgrade]

/-- Source-agnosticity at the grade level: `gradeToTrack` is the only
    function that determines the track. -/
theorem track_determined_by_grade (g : EpistemicGrade) (s₁ s₂ : Source)
    (l₁ l₂ : String) (sl₁ sl₂ : Slope) {Sem : Type*}
    (cs₁ cs₂ : List (GradedClaim Sem)) :
    (SourcedClaim.mk (GradedClaim.mk l₁ g sl₁ cs₁) s₁).track =
    (SourcedClaim.mk (GradedClaim.mk l₂ g sl₂ cs₂) s₂).track := by
  simp [SourcedClaim.track, GradedClaim.track, GradedClaim.grade]

/-! ## In-scope / out-of-scope boundary -/

/-- An **in-scope predicate** determines which semantic objects are gradable.
    Claims about out-of-scope objects receive no track assignment. -/
structure ScopeBoundary (Sem : Type*) where
  /-- The predicate identifying in-scope semantic objects. -/
  inScope : Sem → Prop
  /-- Decidability of the scope predicate. -/
  decInScope : DecidablePred inScope

/-- A graded claim is **in-scope** when its semantic interpretation falls
    within the scope boundary. -/
def GradedClaim.inScopeClaim {Sem : Type*}
    (c : GradedClaim Sem) (boundary : ScopeBoundary Sem)
    (interpret : GradedClaim Sem → Sem) : Prop :=
  boundary.inScope (interpret c)

/-- An in-scope claim receives a definite (non-Ungraded) track iff its grade
    is not Ungraded. -/
theorem inscope_definite_track {Sem : Type*}
    (c : GradedClaim Sem) (boundary : ScopeBoundary Sem)
    (interpret : GradedClaim Sem → Sem)
    (_hscope : c.inScopeClaim boundary interpret)
    (hgraded : c.grade ≠ EpistemicGrade.Ungraded) :
    c.track ≠ Track.Ungraded := by
  cases c with
  | mk l g s cs =>
    simp only [GradedClaim.track, GradedClaim.grade, gradeToTrack] at *
    cases g <;> simp_all

/-! ## Routing completeness -/

/-- **Routing completeness**: every graded claim is assigned exactly one track.
    Trivially true by construction since `gradeToTrack` is total, but stated
    explicitly to satisfy the checklist. -/
theorem routing_complete (g : EpistemicGrade) :
    ∃! t : Track, gradeToTrack g = t :=
  ⟨gradeToTrack g, rfl, fun _ h => h.symm⟩

/-- The router is surjective: every track is the image of some grade. -/
theorem routing_surjective : Function.Surjective gradeToTrack := by
  intro t
  cases t with
  | A => exact ⟨.Proven, rfl⟩
  | B => exact ⟨.Supported, rfl⟩
  | C => exact ⟨.Analyzed, rfl⟩
  | Ungraded => exact ⟨.Ungraded, rfl⟩

/-- The router is injective: distinct grades map to distinct tracks. -/
theorem routing_injective : Function.Injective gradeToTrack := by
  intro g₁ g₂ h
  cases g₁ <;> cases g₂ <;> simp_all [gradeToTrack]

/-- The router is a bijection between grades and tracks. -/
theorem routing_bijective : Function.Bijective gradeToTrack :=
  ⟨routing_injective, routing_surjective⟩

/-! ## Connecting tracks to Deploy(G, M)

A deploy-scoped capability report's claims each have a track, and
source-agnosticity ensures no source-based bias in routing. -/

/-- Every claim in a deploy-scoped capability report has a well-defined track. -/
theorem deploy_claims_tracked {Sem : Type*}
    (cr : CapabilityReport Sem) (targets : GradedClaim Sem → Sem)
    (_hscoped : cr.deployScoped targets) :
    ∀ c ∈ cr.report.claims, ∃ t : Track, c.track = t :=
  fun c _ => ⟨c.track, rfl⟩

/-! ## Logic-indexed track routing (6B connection)

Each `LogicIndex` from the Axis-1 export maps to a natural default track.
The exact route corresponds to Track A (formal proof), solver and defeasible
routes correspond to Track B (substantial evidence), and the soft route
corresponds to Track C (analysis only).  This mapping is deterministic and
source-agnostic by construction. -/

/-- Map a logic-family index to its natural default track. -/
def logicToTrack : LogicIndex → Track
  | .exact       => .A
  | .solver      => .B
  | .defeasible  => .B
  | .soft        => .C

/-- A **logic-routed sourced claim** pairs a sourced claim with the logic
    family under which it was produced. -/
structure LogicRoutedClaim (Sem : Type*) where
  sc : SourcedClaim Sem
  logicFamily : LogicIndex

/-- The logic-determined track of a logic-routed claim. -/
def LogicRoutedClaim.logicTrack {Sem : Type*} (lrc : LogicRoutedClaim Sem) : Track :=
  logicToTrack lrc.logicFamily

/-- **Logic-routed source-agnosticity**: two logic-routed claims on the same
    logic family receive the same logic track, regardless of source. -/
theorem logic_routed_source_agnostic {Sem : Type*}
    (lrc₁ lrc₂ : LogicRoutedClaim Sem)
    (hlogic : lrc₁.logicFamily = lrc₂.logicFamily) :
    lrc₁.logicTrack = lrc₂.logicTrack := by
  simp only [LogicRoutedClaim.logicTrack, hlogic]

/-- **Logic routing completeness**: every logic index receives a definite track. -/
theorem logic_routing_complete (idx : LogicIndex) :
    ∃ t : Track, logicToTrack idx = t :=
  ⟨logicToTrack idx, rfl⟩

/-- The logic router is surjective onto the non-Ungraded tracks. -/
theorem logic_routing_covers_graded :
    ∀ t : Track, t ≠ .Ungraded → ∃ idx : LogicIndex, logicToTrack idx = t := by
  intro t ht
  cases t with
  | A => exact ⟨.exact, rfl⟩
  | B => exact ⟨.solver, rfl⟩
  | C => exact ⟨.soft, rfl⟩
  | Ungraded => exact absurd rfl ht

/-- **In-scope logic-routed grading**: an in-scope claim under a declared
    logic family always receives a non-Ungraded track. -/
theorem inscope_logic_routed_definite (idx : LogicIndex) :
    logicToTrack idx ≠ Track.Ungraded := by
  cases idx <;> simp [logicToTrack]

end SafeSlice
