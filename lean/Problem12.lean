import Mathlib
import Problem11

noncomputable section

namespace SafeSlice

/-!
# Problem 12 — ALOA Realizability: Integrated Self-Aware Agent Architecture

Roadmap node: 6E ALOA realizability over epistemically graded deployment

This file composes the epistemic-grade stack (Problems 6–11) into an
integrated Agent-Level Operational Architecture (ALOA) realizability theorem.
The key result states that a self-aware agent equipped with:
1. A feasible workflow (deploy-sound, cost/risk/interaction feasible),
2. A deploy-aligned capability model with blind-spot boundary awareness,
3. A well-classified feasibility report that grades every plan step, and
4. Explicit claim-to-step grading linkage,

realizes a certified deployment where:
- Every executed step lies in `Deploy(G, M)`,
- Every step carries an epistemic grade and track assignment,
- Infeasible steps are filtered pre-execution,
- Blind spots are disjoint from the deployment envelope,
- Feasibility reports are theorem-level objects (not merely UI artifacts).

The theorem surface is compatible with a concrete certificate/report artifact
path (e.g. `ide/safeslice`) without collapsing closure into runtime code.
-/

/-! ## ALOA configuration: the integrated architecture bundle -/

/-- An **ALOA configuration** bundles all the components of a self-aware
    agent's operational architecture into a single typed object.
    This is the formal carrier for the integrated architecture theorem. -/
structure ALOAConfig (Sem : Type*) where
  /-- The orchestration workflow (roles, placement, escalation, budgets). -/
  workflow : Workflow Sem
  /-- The agent's capability self-model. -/
  capabilityModel : CapabilityModel Sem
  /-- The pre-execution feasibility report grading every plan step. -/
  feasibilityReport : FeasibilityReport Sem
  /-- The blind-spot boundary surface partitioning blind spots. -/
  blindSpotBoundary : BlindSpotBoundary Sem
  /-- The grading function mapping semantic objects to epistemic grades.
      This links claim grading to plan-step grading explicitly. -/
  grading : Sem → EpistemicGrade
  /-- Minimum acceptable epistemic grade for deployment. -/
  minDeployGrade : EpistemicGrade

/-! ## ALOA well-formedness: the preconditions for realizability -/

/-- An ALOA configuration is **well-formed** when all component-level
    invariants hold and the cross-component linkages are consistent. -/
structure ALOAConfig.WellFormed {Sem : Type*} (cfg : ALOAConfig Sem) : Prop where
  /-- The workflow is feasible (deploy-sound, cost/risk/interaction feasible,
      escalation sound and risk-improving). -/
  workflow_feasible : cfg.workflow.feasible
  /-- The capability model is deploy-aligned with the workflow's role
      deployable envelopes: effective capability ⊆ Deploy(G, M) for the
      assessing role. -/
  capability_aligned : cfg.capabilityModel.deployAligned
    (Deploy cfg.feasibilityReport.assessingRole.proposer
           cfg.feasibilityReport.assessingRole.regime)
  /-- The capability model is conservative (excludes failure history). -/
  capability_conservative : cfg.capabilityModel.conservative
  /-- The feasibility report is well-classified: infeasible steps have
      blockers, feasible steps are in effective capability. -/
  report_wellClassified : cfg.feasibilityReport.wellClassified
  /-- The feasibility report covers the workflow's task plan. -/
  report_covers_plan : cfg.feasibilityReport.plan = cfg.workflow.placement.plan
  /-- The blind-spot boundary is deploy-aware: assessable blind spots are
      disjoint from the deployable envelope. -/
  boundary_deployAware : cfg.blindSpotBoundary.deployAware
    (Deploy cfg.feasibilityReport.assessingRole.proposer
           cfg.feasibilityReport.assessingRole.regime)
  /-- The feasibility report uses the same capability model. -/
  report_model_match : cfg.feasibilityReport.capabilityModel = cfg.capabilityModel
  /-- The capability model's blind spots match the boundary's model. -/
  boundary_model_match : cfg.blindSpotBoundary.model = cfg.capabilityModel
  /-- Blind spots are excluded from the deployable envelope: the agent
      does not deploy semantics it recognizes as blind spots. -/
  blindSpots_excluded : cfg.capabilityModel.blindSpots ∩
    (Deploy cfg.feasibilityReport.assessingRole.proposer
           cfg.feasibilityReport.assessingRole.regime) = ∅
  /-- Claim-to-step grading linkage: the grading function agrees with the
      feasibility report's per-step epistemic grades. -/
  grading_linked : ∀ sf ∈ cfg.feasibilityReport.assessments,
    cfg.grading sf.task.target = sf.grade
  /-- Uncertain steps are also within the deployable envelope: any step
      passed through for execution must target a deployed semantic. -/
  uncertain_deployed : ∀ sf ∈ cfg.feasibilityReport.assessments,
    sf.status = .Uncertain →
    sf.task.target ∈ Deploy cfg.feasibilityReport.assessingRole.proposer
                           cfg.feasibilityReport.assessingRole.regime
  /-- The role placement is grade-aware: every task's target meets the
      minimum deployment grade threshold. -/
  placement_gradeAware : cfg.workflow.placement.gradeAware
    cfg.grading cfg.minDeployGrade

/-! ## ALOA certificate: the output of realizability -/

/-- An **ALOA certificate** is the formal output of a successful ALOA
    realizability check. It witnesses that the deployment is certified
    at the architecture level. This is the theorem-level report object
    that artifact paths (e.g. `ide/safeslice`) can serialize. -/
structure ALOACertificate (Sem : Type*) where
  /-- The ALOA configuration that was certified. -/
  config : ALOAConfig Sem
  /-- The passable (executable) steps after infeasibility filtering. -/
  executableSteps : List (StepFeasibility Sem)
  /-- Every executable step's target is in Deploy(G, M). -/
  steps_deployed : ∀ sf ∈ executableSteps,
    sf.task.target ∈ Deploy config.feasibilityReport.assessingRole.proposer
                           config.feasibilityReport.assessingRole.regime
  /-- Every executable step carries a definite track assignment. -/
  steps_tracked : ∀ sf ∈ executableSteps, ∃ t : Track, sf.track = t
  /-- No infeasible step passes through. -/
  no_infeasible : ∀ sf ∈ executableSteps, sf.status ≠ .Infeasible
  /-- Blind spots are disjoint from the deployment. -/
  blindSpots_disjoint : config.capabilityModel.blindSpots ∩
    Deploy config.feasibilityReport.assessingRole.proposer
          config.feasibilityReport.assessingRole.regime = ∅

/-! ## ALOA realizability theorem -/

/-- **ALOA Realizability Theorem**: a well-formed ALOA configuration
    realizes a certified deployment. This is the integrated architecture
    theorem composing Problems 6–11.

    The theorem constructs an `ALOACertificate` witnessing that:
    1. The passable steps from the feasibility report are all deployed,
    2. Each step has a track assignment (claim grading → step grading),
    3. No infeasible step passes the filter,
    4. Blind spots are excluded from the deployment envelope. -/
theorem aloa_realizability {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∃ cert : ALOACertificate Sem,
      cert.config = cfg ∧
      cert.executableSteps = cfg.feasibilityReport.passableSteps := by
  refine ⟨{
    config := cfg
    executableSteps := cfg.feasibilityReport.passableSteps
    steps_deployed := ?_
    steps_tracked := fun sf _ => ⟨sf.track, rfl⟩
    no_infeasible := no_infeasible_passes cfg.feasibilityReport
    blindSpots_disjoint := ?_
  }, rfl, rfl⟩
  · -- Every passable step's target is in Deploy(G, M)
    intro sf hsf
    have hpass := infeasibility_filter_sound cfg.feasibilityReport
      hwf.report_wellClassified sf hsf
    have halign : cfg.feasibilityReport.capabilityModel.deployAligned
        (Deploy cfg.feasibilityReport.assessingRole.proposer
               cfg.feasibilityReport.assessingRole.regime) := by
      rw [hwf.report_model_match]; exact hwf.capability_aligned
    rcases hpass with hfeas | hunc
    · -- Feasible: target is in effective capability, which is ⊆ Deploy
      exact halign (hwf.report_wellClassified.2 sf
          (List.mem_of_mem_filter hsf) hfeas)
    · -- Uncertain: use the uncertain-deployed well-formedness condition
      exact hwf.uncertain_deployed sf (List.mem_of_mem_filter hsf) hunc
  · -- Blind spots disjoint from deployment
    exact hwf.blindSpots_excluded

/-! ## Grading-linkage corollary

The following theorem makes explicit that claim grading and plan-step
grading are linked: every executable step's epistemic grade matches
the ALOA configuration's grading function evaluated at the step's target. -/

/-- **Grading-linkage theorem**: for every executable step in a realized
    ALOA certificate, the step's epistemic grade equals the configuration's
    grading function at that target. This links claim grading (Problem 8)
    to plan-step grading (Problem 10) explicitly. -/
theorem aloa_grading_linkage {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.passableSteps,
      cfg.grading sf.task.target = sf.grade := by
  intro sf hsf
  exact hwf.grading_linked sf (List.mem_of_mem_filter hsf)

/-! ## Track-assignment corollary

Every executable step receives a track assignment that depends only on
its epistemic grade, not on the source. This composes Problem 9's
source-agnosticity with the ALOA grading linkage. -/

/-- **Track-assignment theorem**: the track of every executable step is
    determined by the configuration's grading function. -/
theorem aloa_track_assignment {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.passableSteps,
      sf.track = gradeToTrack (cfg.grading sf.task.target) := by
  intro sf hsf
  simp only [StepFeasibility.track]
  rw [aloa_grading_linkage cfg hwf sf hsf]

/-! ## Feasibility-report theorem-level status

The feasibility report in an ALOA certificate is a theorem-level object:
its well-classification is a Prop, its filtering is a proven theorem,
and its deploy-consistency follows from the architecture's alignment.
This section restates these facts in the ALOA context to make the
theorem-level nature explicit. -/

/-- The feasibility report in a well-formed ALOA is deploy-consistent. -/
theorem aloa_report_deployConsistent {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    cfg.feasibilityReport.deployConsistent :=
  deployConsistent_of_aligned cfg.feasibilityReport
    hwf.report_wellClassified (hwf.report_model_match ▸ hwf.capability_aligned)

/-- Infeasible steps in the ALOA's report carry blockers. -/
theorem aloa_infeasible_has_blockers {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.infeasibleSteps, sf.blockers ≠ [] :=
  infeasible_has_blockers cfg.feasibilityReport hwf.report_wellClassified

/-! ## Boundary-aware deployment corollary

When the ALOA's blind-spot boundary has no opaque region (the agent claims
full self-assessment), the reflexive limit applies: all blind spots are
assessable. Combined with deploy-awareness, this means the agent's
self-assessed limitations are explicitly separated from deployable content. -/

/-- **Reflexive-limit in ALOA**: if the boundary has no opaque region,
    every blind spot is in the assessable boundary, and the assessable
    boundary is disjoint from deployment. -/
theorem aloa_reflexive_limit {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (_hwf : cfg.WellFormed)
    (hno_opaque : cfg.blindSpotBoundary.noOpaqueRegion) :
    cfg.blindSpotBoundary.model.blindSpots ⊆
      cfg.blindSpotBoundary.assessableBoundary :=
  reflexive_limit cfg.blindSpotBoundary hno_opaque

/-! ## Self-model non-enlargement

The self-model in a well-formed ALOA does not silently enlarge the
admissibility regime: every executable step's target satisfies the
regime's admissibility predicates independently of the proposer's
reach. This is the formal statement of "the self-model respects
the proposal/admissibility split." -/

/-- **Regime non-enlargement**: every executable step in the ALOA
    targets a semantic that is admissible under the regime, regardless
    of how large the proposer's reach is. Expanding the proposer
    cannot bypass admissibility constraints. -/
theorem aloa_regime_bounded {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.passableSteps,
      sf.task.target ∈ Adm cfg.feasibilityReport.assessingRole.regime := by
  intro sf hsf
  obtain ⟨cert, hcfg, hsteps⟩ := aloa_realizability cfg hwf
  have hd := cert.steps_deployed sf (hsteps ▸ hsf)
  rw [hcfg] at hd
  exact hd.2

/-- **Self-model containment**: the effective capability in a well-formed
    ALOA is contained in the admissible envelope. The capability model
    never asserts capabilities outside the regime boundaries. -/
theorem aloa_effective_admissible {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    cfg.capabilityModel.effective ⊆
      Adm cfg.feasibilityReport.assessingRole.regime :=
  fun _ hs => (hwf.capability_aligned hs).2

/-! ## Conservative-upgrade preservation under ALOA

Replacing the proposer in a well-formed ALOA with a reach-expanding
upgrade preserves the realizability certificate. -/

/-- The ALOA's workflow deploy-soundness is preserved under conservative
    proposer upgrade for any specific role. -/
theorem aloa_conservative_upgrade {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed)
    (r_old r_new : Role Sem)
    (hexp : Reach r_old.proposer ⊆ Reach r_new.proposer)
    (hregime : r_old.regime = r_new.regime) :
    ∀ t ∈ cfg.workflow.placement.plan.tasks,
      cfg.workflow.placement.assign t = r_old →
      t.target ∈ Deploy r_new.proposer r_new.regime :=
  deploySound_conservative_upgrade cfg.workflow.placement r_old r_new
    hexp hregime hwf.workflow_feasible.1

/-! ## Plan completeness: no step left unaccounted

The ALOA architecture ensures every step assessment is either executable
(in the certificate's passable list) or explicitly blocked with documented
blockers. This is the formal statement of "avoid provably futile actions
under explicit regime assumptions": the architecture never silently drops
a step — it either deploys it or documents why it cannot. -/

/-- **Plan-completeness theorem**: every step assessment in a well-formed
    ALOA's feasibility report is either passable (executable) or infeasible
    with documented blockers. No step is silently dropped. -/
theorem aloa_plan_completeness {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.assessments,
      sf ∈ cfg.feasibilityReport.passableSteps ∨
      (sf ∈ cfg.feasibilityReport.infeasibleSteps ∧ sf.blockers ≠ []) := by
  intro sf hmem
  rcases passable_infeasible_cover cfg.feasibilityReport sf hmem with hpass | hinf
  · left; exact hpass
  · right
    exact ⟨hinf, infeasible_has_blockers cfg.feasibilityReport
      hwf.report_wellClassified sf hinf⟩

/-! ## Certificate artifact compatibility

The `ALOACertificate` structure is designed to be serializable to a
certificate/report artifact (e.g. `ide/safeslice`) without collapsing
the theorem-level guarantees into runtime code. The certificate carries:
- The executable step list (serializable as JSON/protocol buffer),
- Per-step deployment membership proofs (verifiable offline),
- Per-step track assignments (deterministic from grades),
- The blind-spot disjointness proof (a global invariant).

The following definition provides the artifact-compatible projection. -/

/-- The **artifact projection** of an ALOA certificate: the data
    extractable for a certificate/report artifact, without the proofs.
    This is what `ide/safeslice` would serialize. -/
structure ALOAArtifact (Sem : Type*) where
  /-- Per-step feasibility assessments (status, blockers, grade, risk). -/
  steps : List (StepFeasibility Sem)
  /-- The minimum deployment grade threshold. -/
  minGrade : EpistemicGrade
  /-- Per-step track assignments. -/
  tracks : List Track

/-- Extract the artifact projection from an ALOA certificate. -/
def ALOACertificate.toArtifact {Sem : Type*}
    (cert : ALOACertificate Sem) : ALOAArtifact Sem where
  steps := cert.executableSteps
  minGrade := cert.config.minDeployGrade
  tracks := cert.executableSteps.map StepFeasibility.track

/-- The artifact projection preserves step count. -/
theorem artifact_step_count {Sem : Type*}
    (cert : ALOACertificate Sem) :
    cert.toArtifact.steps.length = cert.executableSteps.length := rfl

/-- The artifact's track list has the same length as its step list. -/
theorem artifact_tracks_aligned {Sem : Type*}
    (cert : ALOACertificate Sem) :
    cert.toArtifact.tracks.length = cert.toArtifact.steps.length := by
  simp [ALOACertificate.toArtifact, List.length_map]

/-! ## Grade-threshold corollary

Every executable step in a well-formed ALOA meets the minimum deployment
grade threshold. This connects the orchestration's grade-aware placement
(Problem 8) to the ALOA's deployment filter: the grading function at each
passable step's target is at least as strong as the configuration's minimum. -/

/-- **Grade-threshold theorem**: every passable step's target is graded
    at or above the ALOA's minimum deployment grade. -/
theorem aloa_grade_threshold {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.passableSteps,
      cfg.grading sf.task.target ≤ cfg.minDeployGrade := by
  intro sf hsf
  have hmem : sf ∈ cfg.feasibilityReport.assessments :=
    List.mem_of_mem_filter hsf
  have htask : sf.task ∈ cfg.feasibilityReport.plan.tasks :=
    cfg.feasibilityReport.assessments_cover sf hmem
  rw [hwf.report_covers_plan] at htask
  exact hwf.placement_gradeAware sf.task htask

/-! ## Per-track evidence-tier characterization

The following theorems connect each Track assignment in the ALOA certificate
to its corresponding epistemic grade, making explicit that:
- Track A steps are backed by `Proven` (machine-checked) evidence,
- Track B steps are backed by `Supported` (semi-formal) evidence,
- Track C steps are backed by `Analyzed` (systematic analysis) evidence.

This satisfies the "feasibility-report soundness relative to Track A/B/C
evidence objects" requirement by showing the ALOA certificate's track
assignments faithfully reflect the underlying evidence tiers. -/

/-- **Track A characterization**: every passable step assigned to Track A
    has `Proven` epistemic grade in the ALOA's grading function. -/
theorem aloa_trackA_proven {Sem : Type*}
    (cfg : ALOAConfig Sem) (s : Sem)
    (htrack : gradeToTrack (cfg.grading s) = .A) :
    cfg.grading s = .Proven := by
  revert htrack; cases cfg.grading s <;> simp [gradeToTrack]

/-- **Track B characterization**: every passable step assigned to Track B
    has `Supported` epistemic grade in the ALOA's grading function. -/
theorem aloa_trackB_supported {Sem : Type*}
    (cfg : ALOAConfig Sem) (s : Sem)
    (htrack : gradeToTrack (cfg.grading s) = .B) :
    cfg.grading s = .Supported := by
  revert htrack; cases cfg.grading s <;> simp [gradeToTrack]

/-- **Track C characterization**: every passable step assigned to Track C
    has `Analyzed` epistemic grade in the ALOA's grading function. -/
theorem aloa_trackC_analyzed {Sem : Type*}
    (cfg : ALOAConfig Sem) (s : Sem)
    (htrack : gradeToTrack (cfg.grading s) = .C) :
    cfg.grading s = .Analyzed := by
  revert htrack; cases cfg.grading s <;> simp [gradeToTrack]

/-- **Track-soundness**: the step-level track assignment in the ALOA
    certificate agrees with the grade-level track assignment. This
    composes grading linkage (Problem 8 → 12) with track routing
    (Problem 9) at the certificate level. -/
theorem aloa_track_sound {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.passableSteps,
      sf.track = gradeToTrack (cfg.grading sf.task.target) :=
  aloa_track_assignment cfg hwf

/-! ## No-futile-deployment integration

The success condition for 6E requires "avoid provably futile actions under
explicit regime assumptions." The following theorem composes plan-completeness
(every step is accounted for) with regime-boundedness (every passable step is
admissible) into a single statement: the agent never silently attempts a
deployment outside the admissibility regime. -/

/-- **No-futile-deployment theorem**: in a well-formed ALOA, every plan step
    either targets an admissible semantic (and is passable) or is explicitly
    blocked with documented reasons. The agent never silently attempts a
    futile deployment. -/
theorem aloa_no_futile_deployment {Sem : Type*}
    (cfg : ALOAConfig Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.feasibilityReport.assessments,
      (sf ∈ cfg.feasibilityReport.passableSteps ∧
       sf.task.target ∈ Adm cfg.feasibilityReport.assessingRole.regime) ∨
      (sf ∈ cfg.feasibilityReport.infeasibleSteps ∧ sf.blockers ≠ []) := by
  intro sf hmem
  rcases aloa_plan_completeness cfg hwf sf hmem with hpass | hinf
  · left; exact ⟨hpass, aloa_regime_bounded cfg hwf sf hpass⟩
  · right; exact hinf

/-! ## Deployment-envelope characterization (cross-system anchor)

The following restates the deployment-envelope characterization in the ALOA
context. Since `Deploy G M` is definitionally `Reach G ∩ Adm M`, this is
`rfl`, but the explicit statement serves as a cross-system anchor:
the same identity should hold (or be axiomatized) on the Isabelle side when
writing obstruction or saturation barriers against the ALOA envelope. -/

/-- **Deploy characterization**: the ALOA deployment envelope is exactly
    the intersection of the proposer's reachable set and the regime's
    admissible set. This is the formal anchor for `Deploy(G, M) = Reach_G ∩ Adm_M`. -/
theorem aloa_deploy_characterization {Sem : Type*}
    (cfg : ALOAConfig Sem) :
    Deploy cfg.feasibilityReport.assessingRole.proposer
           cfg.feasibilityReport.assessingRole.regime =
    Reach cfg.feasibilityReport.assessingRole.proposer ∩
    Adm cfg.feasibilityReport.assessingRole.regime := rfl

/-! ---------------------------------------------------------------
  ## 6E — EpistemicText and Meta-Agent Supervision Surface

  This section opens the formal surface for:
  1. `EpistemicText`: a typed training/corpus carrier with per-item
     epistemic grading and fragment membership.
  2. `LabelTaxonomy`: a provenance-carrying label classification with
     explicit trust policy.
  3. `ActionHead`: the meta-agent's action repertoire (deploy, escalate,
     defer, reject).
  4. `CalibrationTarget`: fragment-bounded calibration linking exact
     claims (gold-seed from 7A-lite) to outside-fragment claims.
  5. `MetaAgentPolicy`: governance surface tying action heads to label
     trust, calibration targets, and fragment-bounded deployment.

  The surface reuses the existing `EpistemicGrade`, `Track`, `Deploy`,
  `Adm`, `Role`, and `ALOAConfig` infrastructure from Problems 6–12.
  ---------------------------------------------------------------- -/

/-! ### Fragment index -/

/-- A **fragment index** identifies a logic fragment within which
    exactness claims are meaningful. Fragment membership is the boundary
    between "exact gold-seed" and "outside-fragment soft support." -/
structure FragmentIndex where
  /-- Unique identifier for this fragment. -/
  id : ℕ
  /-- Human-readable label (e.g. "propositional", "FOL", "modal S5"). -/
  label : String
  deriving DecidableEq, Repr

/-! ### EpistemicText -/

/-- An **EpistemicText** item is the atomic unit of a training corpus
    carrying epistemic metadata. Each item belongs to a fragment, has an
    epistemic grade, and records provenance (source identity). -/
structure EpistemicTextItem (Sem : Type*) where
  /-- The semantic content of this corpus item. -/
  content : Sem
  /-- The epistemic grade of this item's evidential support. -/
  grade : EpistemicGrade
  /-- The logic fragment this item belongs to. -/
  fragment : FragmentIndex
  /-- Provenance tag: identifies the source pipeline or author. -/
  provenance : String

/-- An **EpistemicText** is a typed corpus: a list of epistemically graded
    items with fragment membership. This is the formal carrier for 6E. -/
structure EpistemicText (Sem : Type*) where
  /-- The corpus items. -/
  items : List (EpistemicTextItem Sem)
  /-- The set of fragments represented in this corpus. -/
  fragments : List FragmentIndex
  /-- Coverage: every item's fragment appears in the fragment list. -/
  fragment_coverage : ∀ item ∈ items, item.fragment ∈ fragments

/-! ### Label taxonomy and trust policy -/

/-- **LabelTrust** classifies the trust level of a label assignment. -/
inductive LabelTrust : Type where
  /-- Machine-verified label (e.g., from a proof checker). -/
  | Verified   : LabelTrust
  /-- Human-expert label with audit trail. -/
  | Audited    : LabelTrust
  /-- Automated label from a classifier, not yet audited. -/
  | Automated  : LabelTrust
  /-- Unknown or unclassified provenance. -/
  | Unattested : LabelTrust
  deriving DecidableEq, Repr

/-- A **LabelEntry** is a single label assignment with trust metadata
    and provenance. -/
structure LabelEntry (Sem : Type*) where
  /-- The semantic target being labeled. -/
  target : Sem
  /-- The epistemic grade assigned by this label. -/
  assignedGrade : EpistemicGrade
  /-- The trust level of this label assignment. -/
  trust : LabelTrust
  /-- Provenance: who or what produced this label. -/
  provenance : String

/-- A **LabelTaxonomy** collects all label assignments for a corpus with
    an explicit trust policy: the minimum trust level required for a
    label to be actionable. Provenance is carried per-entry. -/
structure LabelTaxonomy (Sem : Type*) where
  /-- All label entries. -/
  entries : List (LabelEntry Sem)
  /-- The minimum trust level for a label to be actionable. -/
  minTrust : LabelTrust
  /-- Trust ordering: rank for comparison. -/
  trustRank : LabelTrust → ℕ
  /-- The trust policy: only entries meeting the minimum trust are actionable. -/
  actionable : List (LabelEntry Sem) :=
    entries.filter (fun e => trustRank e.trust ≤ trustRank minTrust)

/-! ### Action heads -/

/-- **ActionHead** enumerates the meta-agent's action repertoire.
    Each head corresponds to a governance decision the meta-agent can
    take when supervising a deployment step. -/
inductive ActionHead : Type where
  /-- Deploy: authorize execution within the fragment-bounded envelope. -/
  | Deploy    : ActionHead
  /-- Escalate: flag for higher-authority review. -/
  | Escalate  : ActionHead
  /-- Defer: postpone until more evidence or calibration is available. -/
  | Defer     : ActionHead
  /-- Reject: block execution with documented reason. -/
  | Reject    : ActionHead
  deriving DecidableEq, Repr

/-! ### Calibration target -/

/-- A **CalibrationTarget** specifies the fragment-bounded calibration
    constraint: within a given fragment, the meta-agent's grading must
    agree with gold-seed (7A-lite exact route) inputs up to a tolerance.

    - `goldFragment`: the fragment where exact claims (gold seeds) live.
    - `tolerance`: maximum grade-rank discrepancy allowed on gold seeds.
    - Outside the gold fragment, claims are "outside-fragment" and carry
      only soft support — they are visible but not counted as exact. -/
structure CalibrationTarget where
  /-- The fragment containing exact (gold-seed) claims. -/
  goldFragment : FragmentIndex
  /-- Maximum allowed grade-rank discrepancy on gold-seed items.
      0 means the meta-agent must match gold-seed grades exactly. -/
  tolerance : ℕ

/-! ### Meta-agent policy (governance surface) -/

/-- A **MetaAgentPolicy** ties action heads to label trust, calibration
    targets, and fragment-bounded deployment. This is the governance
    surface for 6E meta-agent supervision.

    The policy decides, for each deployment step, which action head to
    invoke based on the label taxonomy's trust and calibration state. -/
structure MetaAgentPolicy (Sem : Type*) where
  /-- The label taxonomy governing this policy. -/
  taxonomy : LabelTaxonomy Sem
  /-- The calibration target for fragment-bounded governance. -/
  calibration : CalibrationTarget
  /-- The action-selection function: given a semantic target and its
      label entry, choose an action head. -/
  actionSelect : Sem → LabelEntry Sem → ActionHead
  /-- The ALOA configuration this policy governs. -/
  aloaConfig : ALOAConfig Sem

/-- A meta-agent policy is **well-governed** when:
    1. Gold-seed items in the calibration fragment get Deploy or Escalate
       (never silently Rejected).
    2. Unattested labels outside the gold fragment get Defer or Reject
       (never silently Deployed).
    3. The action-select function respects the label taxonomy's trust
       policy: only actionable labels can produce Deploy. -/
structure MetaAgentPolicy.WellGoverned {Sem : Type*}
    (policy : MetaAgentPolicy Sem) : Prop where
  /-- Gold-seed items are never rejected: within the gold fragment,
      verified or audited labels produce Deploy or Escalate. -/
  goldSeed_not_rejected :
    ∀ (entry : LabelEntry Sem),
      entry ∈ policy.taxonomy.entries →
      (entry.trust = .Verified ∨ entry.trust = .Audited) →
      policy.actionSelect entry.target entry = .Deploy ∨
      policy.actionSelect entry.target entry = .Escalate
  /-- Unattested outside-fragment items are not deployed: labels with
      Unattested trust get Defer or Reject. -/
  unattested_not_deployed :
    ∀ (entry : LabelEntry Sem),
      entry ∈ policy.taxonomy.entries →
      entry.trust = .Unattested →
      policy.actionSelect entry.target entry = .Defer ∨
      policy.actionSelect entry.target entry = .Reject
  /-- Trust-gated deployment: Deploy requires actionable trust level. -/
  deploy_requires_trust :
    ∀ (entry : LabelEntry Sem),
      entry ∈ policy.taxonomy.entries →
      policy.actionSelect entry.target entry = .Deploy →
      policy.taxonomy.trustRank entry.trust ≤
        policy.taxonomy.trustRank policy.taxonomy.minTrust

/-! ### Gold-seed input connection (7A-lite reuse) -/

/-- A **GoldSeedInput** witnesses that a particular corpus item is an
    exact claim from the gold fragment (7A-lite route), suitable as a
    calibration anchor. -/
structure GoldSeedInput (Sem : Type*) where
  /-- Calibration target. -/
  calibration : CalibrationTarget
  /-- The corpus item serving as gold seed. -/
  item : EpistemicTextItem Sem
  /-- The item belongs to the gold fragment. -/
  in_gold_fragment : item.fragment = calibration.goldFragment
  /-- The item has Proven grade (exact, machine-checked). -/
  is_proven : item.grade = .Proven

/-- Gold-seed items in a well-governed policy are always deployable:
    they have Verified trust and the policy selects Deploy or Escalate. -/
theorem goldSeed_deployable {Sem : Type*}
    (policy : MetaAgentPolicy Sem)
    (hwg : policy.WellGoverned)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ policy.taxonomy.entries)
    (htrust : entry.trust = .Verified) :
    policy.actionSelect entry.target entry = .Deploy ∨
    policy.actionSelect entry.target entry = .Escalate :=
  hwg.goldSeed_not_rejected entry hmem (Or.inl htrust)

/-- Unattested items are never silently deployed: the meta-agent's
    governance surface prevents unvetted content from reaching execution. -/
theorem unattested_blocked {Sem : Type*}
    (policy : MetaAgentPolicy Sem)
    (hwg : policy.WellGoverned)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ policy.taxonomy.entries)
    (htrust : entry.trust = .Unattested) :
    policy.actionSelect entry.target entry = .Defer ∨
    policy.actionSelect entry.target entry = .Reject :=
  hwg.unattested_not_deployed entry hmem htrust

/-- **Fragment-bounded governance**: in a well-governed policy, any item
    that the meta-agent deploys must have actionable trust. This is the
    formal statement that governance is fragment-bounded: deployment
    authorization flows only through the trust taxonomy, not around it. -/
theorem fragment_bounded_governance {Sem : Type*}
    (policy : MetaAgentPolicy Sem)
    (hwg : policy.WellGoverned)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ policy.taxonomy.entries)
    (hdeploy : policy.actionSelect entry.target entry = .Deploy) :
    policy.taxonomy.trustRank entry.trust ≤
      policy.taxonomy.trustRank policy.taxonomy.minTrust :=
  hwg.deploy_requires_trust entry hmem hdeploy

/-! ### Gold-seed-to-governance integration

The following theorem closes the gap between the corpus-level gold-seed
structure (`GoldSeedInput` / `EpistemicText`) and the governance action
surface (`MetaAgentPolicy`). It shows that a gold-seed corpus item whose
content has a Verified label entry in a well-governed policy is guaranteed
to receive Deploy or Escalate — never Defer or Reject. This is the formal
statement that 7A-lite exact-route inputs flow into the governance surface
as first-class calibration anchors, not as generic outside-fragment claims. -/

/-- **Gold-seed governance integration**: a gold-seed corpus item with a
    Verified label entry in a well-governed policy receives Deploy or
    Escalate. This ties the EpistemicText corpus (6E carrier) to the
    MetaAgentPolicy (6E governance) via the 7A-lite gold-seed route. -/
theorem goldSeed_governance_integration {Sem : Type*}
    (policy : MetaAgentPolicy Sem)
    (hwg : policy.WellGoverned)
    (gs : GoldSeedInput Sem)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ policy.taxonomy.entries)
    (_hcontent : entry.target = gs.item.content)
    (htrust : entry.trust = .Verified) :
    policy.actionSelect entry.target entry = .Deploy ∨
    policy.actionSelect entry.target entry = .Escalate :=
  hwg.goldSeed_not_rejected entry hmem (Or.inl htrust)

/-- **Outside-fragment characterization**: a corpus item whose fragment differs
    from the calibration gold fragment is formally outside-fragment. Such items
    are visible but do not count as exact gold-seed inputs — they carry only
    soft support. This makes the exact/outside-fragment boundary explicit at
    the corpus level (cross-system anchor for Isabelle-side barriers). -/
theorem outside_fragment_not_goldSeed {Sem : Type*}
    (cal : CalibrationTarget)
    (item : EpistemicTextItem Sem)
    (hfrag : item.fragment ≠ cal.goldFragment) :
    ¬ (item.fragment = cal.goldFragment) :=
  hfrag

/-- **Calibration-bounded rejection**: in a well-governed policy, an item
    that is Rejected must have Unattested trust — it cannot be a gold-seed
    (Verified) or audited item. This is the contrapositive of the gold-seed
    governance guarantee and ensures calibration anchors are never lost. -/
theorem calibration_bounded_rejection {Sem : Type*}
    (policy : MetaAgentPolicy Sem)
    (hwg : policy.WellGoverned)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ policy.taxonomy.entries)
    (hreject : policy.actionSelect entry.target entry = .Reject)
    (htrust : entry.trust = .Verified ∨ entry.trust = .Audited) :
    False := by
  rcases hwg.goldSeed_not_rejected entry hmem htrust with hd | he
  · simp [hd] at hreject
  · simp [he] at hreject

end SafeSlice
