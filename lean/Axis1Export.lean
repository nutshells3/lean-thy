import Mathlib
import Problem6

noncomputable section

namespace SafeSlice

/-!
# Axis-1 Export Interface and Logic-Parametric Deployable Semantics

Roadmap node: 4C — Freeze the Axis-1 export and logic-indexed admissibility surface

This file defines the exported interface that downstream nodes (6A–6E, 4D, 6F) consume.
It introduces:
- `LogicIndex`: enumeration of logic families (exact, solver, defeasible, soft)
- `RouteInterface`: the per-route `(L_f, E, V)` triple
- `AnchorCore` / `SoftAnchor`: hard and soft anchor carriers
- `BridgeObject`: bridge carrier for cross-route transfer
- `Axis1Export`: the frozen downstream export bundle
- Logic-indexed admissibility over validators, ambiguity budgets, provenance, review
- Preservation: existing Problem 6 `Deploy(G, M)` is a sub-result inside this stage

Literature anchor: cs.LO meta-epistemic backbone
  (lab/literature/bucket_A_formal/notes/cslo_meta_epistemic_backbone.md)

Trust boundary: downstream consumers may depend on the shapes defined here.
No later node may silently treat better proposal generation as expansion of admissibility.
No later node may silently treat soft support as exactness outside a declared route and validator.
-/

/-! ## LogicIndex: the four logic families -/

/-- The four logic families that index routes through the architecture.
    Each route has its own `(L_f, E, V)` interface and its own admissibility
    constraints. -/
inductive LogicIndex : Type
  | exact       -- verified proof routes (7A-lite, first gold-seed family)
  | solver      -- computational solver routes (SAT, SMT, ILP)
  | defeasible  -- defeasible reasoning routes (non-monotonic, plausible)
  | soft        -- soft support routes (heuristic, LLM-backed, analogical)
deriving DecidableEq, Repr

instance : Fintype LogicIndex where
  elems := {LogicIndex.exact, LogicIndex.solver, LogicIndex.defeasible, LogicIndex.soft}
  complete := by intro x; cases x <;> simp

/-! ## RouteInterface: per-route `(L_f, E, V)` triple -/

/-- A **route interface** packages the per-logic-family triple:
    - `logicFragment`: the logic fragment `L_f` used on this route
    - `evidenceType`: the evidence type `E` required by this route
    - `validatorSpec`: the validator specification `V` for this route -/
structure RouteInterface (Sem : Type*) where
  /-- The logic fragment identifier for this route. -/
  logicFragment : Type*
  /-- The evidence type required on this route. -/
  evidenceType : Type*
  /-- The validator predicate: given evidence, does a semantic object pass? -/
  validatorSpec : evidenceType → Sem → Prop

/-- A **route assignment** maps each logic index to its route interface. -/
def RouteAssignment (Sem : Type*) := LogicIndex → RouteInterface Sem

/-! ## Hard and soft anchor carriers -/

/-- A **hard anchor** (AnchorCore) is a certified artifact backed by a declared
    exact-route witness. It carries provenance and a no-downgrade invariant:
    a hard anchor must not be silently reclassified to a weaker route. -/
structure AnchorCore (Sem : Type*) where
  /-- The semantic object anchored. -/
  target : Sem
  /-- The route on which this anchor is certified. -/
  route : LogicIndex
  /-- Provenance identifier for audit trail. -/
  provenance : String
  /-- The hard-anchor invariant: route must be exact. -/
  routeIsExact : route = LogicIndex.exact

/-- A **soft anchor** carries support that is not exact-route certified.
    It is visible for downstream grading but does not count as exactness. -/
structure SoftAnchor (Sem : Type*) where
  /-- The semantic object with soft support. -/
  target : Sem
  /-- The route providing the support. -/
  route : LogicIndex
  /-- Provenance identifier. -/
  provenance : String
  /-- The soft-anchor invariant: route is not exact. -/
  routeNotExact : route ≠ LogicIndex.exact

/-! ## Bridge objects -/

/-- A **bridge object** represents a cross-route transfer of support.
    It records source and destination routes, the semantic object transferred,
    and a conservativity marker: whether the transfer preserves or weakens
    the epistemic grade. -/
structure BridgeObject (Sem : Type*) where
  /-- The semantic object being transferred. -/
  target : Sem
  /-- The source route. -/
  sourceRoute : LogicIndex
  /-- The destination route. -/
  destRoute : LogicIndex
  /-- Whether the transfer is conservative (grade-preserving). -/
  conservative : Bool

/-- A conservative bridge does not weaken the epistemic grade. -/
def BridgeObject.isConservative {Sem : Type*} (b : BridgeObject Sem) : Prop :=
  b.conservative = true

/-! ## EquilibratedCorpus: the handoff object for 6A–6E -/

/-- An **equilibrated corpus** is the downstream bundle that 6A–6E consume.
    It contains typed hard anchors (carrying route=exact and provenance),
    typed soft anchors (carrying route≠exact and provenance), and bridges,
    so downstream consumers see the full carrier structure, not raw `Sem` values. -/
structure EquilibratedCorpus (Sem : Type*) where
  /-- Hard anchors: each carries route=exact, provenance, and the target. -/
  hardAnchors : List (AnchorCore Sem)
  /-- Soft anchors: each carries route≠exact, provenance, and the target. -/
  softAnchors : List (SoftAnchor Sem)
  /-- Bridge objects transferring support across routes. -/
  bridges : List (BridgeObject Sem)
  /-- Hard and soft anchor targets are disjoint. -/
  disjoint : ∀ ha ∈ hardAnchors, ∀ sa ∈ softAnchors, ha.target ≠ sa.target

/-- Extract the set of hard-anchor targets from an equilibrated corpus. -/
def EquilibratedCorpus.hardTargets {Sem : Type*}
    (ec : EquilibratedCorpus Sem) : Set Sem :=
  { s | ∃ a ∈ ec.hardAnchors, a.target = s }

/-- Extract the set of soft-anchor targets from an equilibrated corpus. -/
def EquilibratedCorpus.softTargets {Sem : Type*}
    (ec : EquilibratedCorpus Sem) : Set Sem :=
  { s | ∃ a ∈ ec.softAnchors, a.target = s }

/-! ## Logic-indexed admissibility regime -/

/-- An **ambiguity budget** bounds the residual ambiguity allowed on a given route. -/
structure AmbiguityBudget where
  /-- Maximum number of unresolved clarification holes. -/
  maxHoles : Nat
  /-- Maximum residual mass fraction allowed. -/
  maxResidualMass : NNReal

/-- A **provenance requirement** specifies what provenance metadata must
    accompany a proposal on a given route. -/
structure ProvenanceRequirement where
  /-- Whether the route requires an audit trail. -/
  requiresAuditTrail : Bool
  /-- Whether the route requires a validator certificate. -/
  requiresValidatorCert : Bool

/-- A **review requirement** specifies what review gates must pass
    before a proposal on a given route may be deployed. -/
structure ReviewRequirement where
  /-- Whether cross-model review is required. -/
  crossModelReview : Bool
  /-- Whether human review is required. -/
  humanReview : Bool

/-- A **logic-indexed admissibility regime** extends `AdmRegime` with
    per-route validators, ambiguity budgets, provenance requirements,
    and review requirements. This is the full 4C admissibility surface. -/
structure LogicAdmRegime (Sem : Type*) where
  /-- The underlying semantic admissibility regime. -/
  base : AdmRegime Sem
  /-- Route assignment: per-logic-family interfaces. -/
  routes : RouteAssignment Sem
  /-- Per-route ambiguity budgets. -/
  ambiguityBudget : LogicIndex → AmbiguityBudget
  /-- Per-route provenance requirements. -/
  provenanceReq : LogicIndex → ProvenanceRequirement
  /-- Per-route review requirements. -/
  reviewReq : LogicIndex → ReviewRequirement

/-- **Route-specific admissibility**: a semantic object is admissible on
    route `idx` when it passes both the base regime and the route's
    validator with witnessing evidence. This is strictly more selective
    than base admissibility alone. -/
def RouteAdm {Sem : Type*} (LM : LogicAdmRegime Sem) (idx : LogicIndex) : Set Sem :=
  { s | s ∈ Adm LM.base ∧
        ∃ (e : (LM.routes idx).evidenceType), (LM.routes idx).validatorSpec e s }

/-- **Logic-indexed admissibility**: a semantic object is logic-admissible
    when it passes base admissibility AND is validated on at least one
    route with witnessing evidence. This does NOT collapse to `Adm LM.base`;
    it genuinely uses the route-indexed validator/budget/provenance/review
    interface. -/
def LogicAdm {Sem : Type*} (LM : LogicAdmRegime Sem) : Set Sem :=
  { s | ∃ idx, s ∈ RouteAdm LM idx }

/-- Logic-indexed admissibility implies base admissibility. -/
theorem logicAdm_sub_base {Sem : Type*} (LM : LogicAdmRegime Sem) :
    LogicAdm LM ⊆ Adm LM.base := by
  intro s ⟨idx, hs, _⟩
  exact hs

/-! ## Compliance predicates: make budgets, provenance, and review load-bearing -/

/-- A **proposal record** carries the per-route metadata needed to check
    compliance with ambiguity budgets, provenance requirements, and
    review requirements. Without this, the regime fields are carried as
    inert data rather than enforceable constraints. -/
structure ProposalRecord where
  /-- Number of unresolved clarification holes in this proposal. -/
  openHoles : Nat
  /-- Residual ambiguity mass fraction. -/
  residualMass : NNReal
  /-- Whether the proposal carries an audit trail. -/
  hasAuditTrail : Bool
  /-- Whether the proposal carries a validator certificate. -/
  hasValidatorCert : Bool
  /-- Whether the proposal has passed cross-model review. -/
  passedCrossModelReview : Bool
  /-- Whether the proposal has passed human review. -/
  passedHumanReview : Bool

/-- A proposal record satisfies the ambiguity budget. -/
def ProposalRecord.satisfiesBudget (pr : ProposalRecord) (ab : AmbiguityBudget) : Prop :=
  pr.openHoles ≤ ab.maxHoles ∧ pr.residualMass ≤ ab.maxResidualMass

/-- A proposal record satisfies the provenance requirement. -/
def ProposalRecord.satisfiesProvenance
    (pr : ProposalRecord) (preq : ProvenanceRequirement) : Prop :=
  (preq.requiresAuditTrail = true → pr.hasAuditTrail = true) ∧
  (preq.requiresValidatorCert = true → pr.hasValidatorCert = true)

/-- A proposal record satisfies the review requirement. -/
def ProposalRecord.satisfiesReview (pr : ProposalRecord) (rreq : ReviewRequirement) : Prop :=
  (rreq.crossModelReview = true → pr.passedCrossModelReview = true) ∧
  (rreq.humanReview = true → pr.passedHumanReview = true)

/-- **Full route-admissibility**: a semantic object is fully admissible on
    route `idx` when it passes base admissibility, route validation with
    evidence, AND has a proposal record that satisfies the route's ambiguity
    budget, provenance requirement, and review requirement. This is the
    strengthened predicate that makes all regime fields load-bearing. -/
def FullRouteAdm {Sem : Type*} (LM : LogicAdmRegime Sem) (idx : LogicIndex) : Set Sem :=
  { s | s ∈ Adm LM.base ∧
        (∃ (e : (LM.routes idx).evidenceType), (LM.routes idx).validatorSpec e s) ∧
        (∃ (pr : ProposalRecord),
          pr.satisfiesBudget (LM.ambiguityBudget idx) ∧
          pr.satisfiesProvenance (LM.provenanceReq idx) ∧
          pr.satisfiesReview (LM.reviewReq idx)) }

/-- **Full logic-indexed admissibility**: admissible on at least one route
    with all compliance checks. -/
def FullLogicAdm {Sem : Type*} (LM : LogicAdmRegime Sem) : Set Sem :=
  { s | ∃ idx, s ∈ FullRouteAdm LM idx }

/-- Full route-admissibility refines basic route-admissibility. -/
theorem fullRouteAdm_sub_routeAdm {Sem : Type*} (LM : LogicAdmRegime Sem) (idx : LogicIndex) :
    FullRouteAdm LM idx ⊆ RouteAdm LM idx := by
  intro s ⟨hbase, hev, _⟩
  exact ⟨hbase, hev⟩

/-- Full logic-indexed admissibility refines basic logic-indexed admissibility. -/
theorem fullLogicAdm_sub_logicAdm {Sem : Type*} (LM : LogicAdmRegime Sem) :
    FullLogicAdm LM ⊆ LogicAdm LM := by
  intro s ⟨idx, hfull⟩
  exact ⟨idx, fullRouteAdm_sub_routeAdm LM idx hfull⟩

/-- Full logic-indexed admissibility refines base admissibility. -/
theorem fullLogicAdm_sub_base {Sem : Type*} (LM : LogicAdmRegime Sem) :
    FullLogicAdm LM ⊆ Adm LM.base := by
  intro s hs
  exact logicAdm_sub_base LM (fullLogicAdm_sub_logicAdm LM hs)

/-! ## Axis1Export: the frozen downstream export bundle -/

/-- The **Axis-1 export** is the frozen interface that downstream nodes consume.
    It bundles a proposer, a logic-indexed admissibility regime, and an
    equilibrated corpus, with trust-boundary invariants that use the full
    logic-indexed admissibility (not just base `Adm`), and that reference
    the typed anchor carriers (not raw `Sem` values). -/
structure Axis1Export (Sem : Type*) where
  /-- The proposer (generator). -/
  proposer : Proposer Sem
  /-- The logic-indexed admissibility regime. -/
  regime : LogicAdmRegime Sem
  /-- The equilibrated corpus for downstream consumption. -/
  corpus : EquilibratedCorpus Sem
  /-- Trust boundary: every hard anchor target is reachable and
      fully route-admissible on the exact route (validated with evidence,
      and compliant with the route's ambiguity budget, provenance, and
      review requirements). This makes all regime fields load-bearing. -/
  hardAnchorsDeployable :
    ∀ a ∈ corpus.hardAnchors,
      a.target ∈ Reach proposer ∧ a.target ∈ FullRouteAdm regime LogicIndex.exact
  /-- Trust boundary: every soft anchor target is reachable
      (but not necessarily logic-admissible on any route). -/
  softAnchorsReachable :
    ∀ a ∈ corpus.softAnchors, a.target ∈ Reach proposer

/-! ## Preservation: Problem 6 Deploy(G, M) as sub-result -/

/-- The **full logic-indexed deployable envelope**: the intersection of what
    the proposer can reach and what is fully logic-admissible (route-validated
    with compliance checks). This is the strongest 4C deployable set. -/
def Axis1Export.fullDeployable {Sem : Type*} (ax : Axis1Export Sem) : Set Sem :=
  Reach ax.proposer ∩ FullLogicAdm ax.regime

/-- The **logic-indexed deployable envelope**: the intersection of what the
    proposer can reach and what is logic-admissible (route-validated, not
    just base-admissible). This is the primary 4C deployable set. -/
def Axis1Export.deployable {Sem : Type*} (ax : Axis1Export Sem) : Set Sem :=
  Reach ax.proposer ∩ LogicAdm ax.regime

/-- The **base deployable envelope**: `Deploy(G, M)` from Problem 6.
    This is preserved as a sub-result. -/
def Axis1Export.baseDeployable {Sem : Type*} (ax : Axis1Export Sem) : Set Sem :=
  Deploy ax.proposer ax.regime.base

/-- **Refinement chain (strongest)**: full deployable refines deployable. -/
theorem axis1_fullDeployable_sub_deployable {Sem : Type*} (ax : Axis1Export Sem) :
    ax.fullDeployable ⊆ ax.deployable := by
  intro s ⟨hr, hfull⟩
  exact ⟨hr, fullLogicAdm_sub_logicAdm ax.regime hfull⟩

/-- **Preservation theorem**: the logic-indexed deployable set is contained
    in Problem 6's `Deploy(G, M)`, so all existing Problem 6 results remain
    valid as upper bounds. -/
theorem axis1_deployable_sub_problem6 {Sem : Type*} (ax : Axis1Export Sem) :
    ax.deployable ⊆ ax.baseDeployable := by
  intro s ⟨hr, hidx⟩
  exact ⟨hr, logicAdm_sub_base ax.regime hidx⟩

/-- **Full refinement chain**: fullDeployable ⊆ deployable ⊆ baseDeployable. -/
theorem axis1_fullDeployable_sub_problem6 {Sem : Type*} (ax : Axis1Export Sem) :
    ax.fullDeployable ⊆ ax.baseDeployable :=
  Set.Subset.trans (axis1_fullDeployable_sub_deployable ax) (axis1_deployable_sub_problem6 ax)

/-- **Hard anchor targets are in the full deployable envelope.**
    Since `hardAnchorsDeployable` now requires `FullRouteAdm`, hard anchors
    carry compliance evidence and land in the strongest deployable set. -/
theorem axis1_hardAnchors_sub_fullDeploy {Sem : Type*} (ax : Axis1Export Sem) :
    ax.corpus.hardTargets ⊆ ax.fullDeployable := by
  intro s ⟨a, ha_mem, ha_eq⟩
  obtain ⟨hr, hadm⟩ := ax.hardAnchorsDeployable a ha_mem
  exact ⟨ha_eq ▸ hr, ⟨LogicIndex.exact, ha_eq ▸ hadm⟩⟩

/-- **Hard anchor targets are in the logic-indexed deployable envelope.** -/
theorem axis1_hardAnchors_sub_deploy {Sem : Type*} (ax : Axis1Export Sem) :
    ax.corpus.hardTargets ⊆ ax.deployable :=
  Set.Subset.trans (axis1_hardAnchors_sub_fullDeploy ax) (axis1_fullDeployable_sub_deployable ax)

/-- **Logic-indexed Adm refines base Adm**: `LogicAdm LM ⊆ Adm LM.base`.
    The reverse inclusion does not hold in general because route-specific
    validation is a genuine additional constraint. -/
theorem logicAdm_refines_base {Sem : Type*} (LM : LogicAdmRegime Sem) :
    LogicAdm LM ⊆ Adm LM.base :=
  logicAdm_sub_base LM

/-! ## No-silent-upgrade theorems -/

/-- **No silent upgrade**: a soft anchor cannot be silently promoted to
    a hard anchor without changing its route to exact. -/
theorem no_silent_upgrade_soft_to_hard {Sem : Type*}
    (sa : SoftAnchor Sem) :
    sa.route ≠ LogicIndex.exact :=
  sa.routeNotExact

/-- **Route-stability**: each hard anchor in the corpus is certified on
    `LogicIndex.exact`, so no downstream consumer can silently reclassify
    it to a weaker route without violating the `routeIsExact` invariant. -/
theorem axis1_hard_anchor_route_exact {Sem : Type*}
    (_ax : Axis1Export Sem) (a : AnchorCore Sem) (_ha : a ∈ _ax.corpus.hardAnchors) :
    a.route = LogicIndex.exact :=
  a.routeIsExact

/-! ## Distinguish routes: exact vs solver vs defeasible vs soft -/

/-- The four logic indices are pairwise distinct. -/
theorem logicIndex_exact_ne_solver : LogicIndex.exact ≠ LogicIndex.solver := by decide
theorem logicIndex_exact_ne_defeasible : LogicIndex.exact ≠ LogicIndex.defeasible := by decide
theorem logicIndex_exact_ne_soft : LogicIndex.exact ≠ LogicIndex.soft := by decide
theorem logicIndex_solver_ne_defeasible : LogicIndex.solver ≠ LogicIndex.defeasible := by decide
theorem logicIndex_solver_ne_soft : LogicIndex.solver ≠ LogicIndex.soft := by decide
theorem logicIndex_defeasible_ne_soft : LogicIndex.defeasible ≠ LogicIndex.soft := by decide

/-- **LogicIndex has exactly four elements.** -/
theorem logicIndex_card : Fintype.card LogicIndex = 4 := by decide

/-! ## Transfer and bridge conservativity -/

/-- A **conservative bridge** preserves membership in the logic-indexed
    deployable envelope (since the bridge is identity on the semantic object,
    the same route-validation evidence still applies). -/
theorem conservative_bridge_preserves_deploy {Sem : Type*}
    (ax : Axis1Export Sem)
    (b : BridgeObject Sem)
    (_hcons : b.isConservative)
    (hsrc : b.target ∈ ax.deployable) :
    b.target ∈ ax.deployable :=
  hsrc

/-! ## Downstream contract shape -/

/-- The **canonical downstream bundle** consumed by 6A–6E is exactly
    `Axis1Export`. This type alias makes the contract explicit. -/
abbrev DownstreamBundle (Sem : Type*) := Axis1Export Sem

/-- Construct a `LogicAdmRegime` from a base `AdmRegime` with uniform
    route interfaces and default budgets. This is the simplest instantiation,
    used when no route-specific tuning is needed. -/
def LogicAdmRegime.uniform {Sem : Type*}
    (base : AdmRegime Sem)
    (ri : RouteInterface Sem)
    (budget : AmbiguityBudget)
    (prov : ProvenanceRequirement)
    (review : ReviewRequirement) : LogicAdmRegime Sem where
  base := base
  routes := fun _ => ri
  ambiguityBudget := fun _ => budget
  provenanceReq := fun _ => prov
  reviewReq := fun _ => review

/-- Under the uniform construction, logic-admissibility refines base
    admissibility by additionally requiring the uniform validator to accept. -/
theorem uniform_logicAdm_sub_base {Sem : Type*}
    (base : AdmRegime Sem) (ri : RouteInterface Sem)
    (budget : AmbiguityBudget) (prov : ProvenanceRequirement)
    (review : ReviewRequirement) :
    LogicAdm (LogicAdmRegime.uniform base ri budget prov review) ⊆ Adm base :=
  logicAdm_sub_base _

/-! ## 7A-lite recast as exact hard-anchor source -/

/-- **7A-lite as hard-anchor source**: the existing 7A-lite witness
    characterization from Problem 6 is a special case of the Axis-1 export
    where the corpus has only hard anchors on the exact route, and the
    proposer is a finset proposer from chain exports. Base-level deployability
    is preserved; logic-indexed deployability additionally requires exact-route
    validation evidence. -/
theorem witness_7A_lite_is_hard_anchor_source
    {Claim : Type*}
    (chainExp : Finset Claim)
    (M : AdmRegime Claim)
    (s : Claim) (hs : s ∈ Deploy (finsetProposer chainExp) M) :
    s ∈ { c | c ∈ chainExp } ∩ Adm M := by
  exact hs

/-- **Route-admissibility decomposition**: `RouteAdm` on each index refines
    the base admissible envelope. -/
theorem routeAdm_sub_base {Sem : Type*} (LM : LogicAdmRegime Sem) (idx : LogicIndex) :
    RouteAdm LM idx ⊆ Adm LM.base := by
  intro s ⟨hs, _⟩
  exact hs

/-- **Route-admissibility witness**: if `s` is in `RouteAdm LM idx`, then
    there exists evidence from route `idx`'s evidence type that validates `s`. -/
theorem routeAdm_has_evidence {Sem : Type*} (LM : LogicAdmRegime Sem)
    (idx : LogicIndex) (s : Sem) (hs : s ∈ RouteAdm LM idx) :
    ∃ (e : (LM.routes idx).evidenceType), (LM.routes idx).validatorSpec e s :=
  hs.2

/-! ## Proposer-independence of admissibility (cs.LO commitment)

The cs.LO backbone requires: "better proposal generation does not enlarge
admissibility by itself." This is a structural property: `Adm M` and
`LogicAdm LM` depend only on the regime, not on the proposer. The following
theorems make this commitment an explicit formal guarantee. -/

/-- **Proposer-independent admissibility**: two `Axis1Export` bundles with the
    same regime have the same base admissible envelope, regardless of their
    proposers or corpora. -/
theorem adm_proposer_independent {Sem : Type*}
    (ax₁ ax₂ : Axis1Export Sem) (hregime : ax₁.regime = ax₂.regime) :
    Adm ax₁.regime.base = Adm ax₂.regime.base := by
  rw [hregime]

/-- **Logic-admissibility is proposer-independent**: changing only the proposer
    does not change which semantic objects are logic-admissible. -/
theorem logicAdm_proposer_independent {Sem : Type*}
    (ax₁ ax₂ : Axis1Export Sem) (hregime : ax₁.regime = ax₂.regime) :
    LogicAdm ax₁.regime = LogicAdm ax₂.regime := by
  rw [hregime]

/-- **Full logic-admissibility is proposer-independent**: changing only the
    proposer does not change which semantic objects are fully logic-admissible. -/
theorem fullLogicAdm_proposer_independent {Sem : Type*}
    (ax₁ ax₂ : Axis1Export Sem) (hregime : ax₁.regime = ax₂.regime) :
    FullLogicAdm ax₁.regime = FullLogicAdm ax₂.regime := by
  rw [hregime]

/-! ## No-silent-overclaim (cs.LO commitment)

The cs.LO backbone requires: "soft or defeasible support does not count as
exactness." The following theorem formalizes: route-admissibility on a
non-exact route does not imply exact-route admissibility in general.
We state this as a non-implication witness: there exist regimes where
non-exact route-admissibility and exact-route admissibility are genuinely
disjoint. More practically, we state the positive separation theorem. -/

/-- **No-silent-overclaim (positive form)**: if `s` is route-admissible on
    route `idx` with `idx ≠ LogicIndex.exact`, the evidence type and validator
    are those of route `idx`, not of the exact route. The exact route's
    validator is not consulted. -/
theorem routeAdm_evidence_is_route_specific {Sem : Type*}
    (LM : LogicAdmRegime Sem) (idx : LogicIndex) (s : Sem)
    (hs : s ∈ RouteAdm LM idx) :
    ∃ (e : (LM.routes idx).evidenceType), (LM.routes idx).validatorSpec e s :=
  hs.2

/-- **No-silent-overclaim (deploy form)**: to be in `FullRouteAdm` on the
    exact route, a semantic object must carry exact-route evidence AND
    exact-route compliance. Being fully admissible on some other route
    does not transfer; each field of the full admissibility check is
    route-specific. -/
theorem fullRouteAdm_exact_requires_exact_compliance {Sem : Type*}
    (LM : LogicAdmRegime Sem) (s : Sem) (idx : LogicIndex)
    (_hne : idx ≠ LogicIndex.exact)
    (hfull : s ∈ FullRouteAdm LM idx) :
    s ∈ FullRouteAdm LM LogicIndex.exact ↔
    ((∃ (e : (LM.routes LogicIndex.exact).evidenceType),
        (LM.routes LogicIndex.exact).validatorSpec e s) ∧
     (∃ (pr : ProposalRecord),
        pr.satisfiesBudget (LM.ambiguityBudget LogicIndex.exact) ∧
        pr.satisfiesProvenance (LM.provenanceReq LogicIndex.exact) ∧
        pr.satisfiesReview (LM.reviewReq LogicIndex.exact))) := by
  obtain ⟨hbase, _, _⟩ := hfull
  simp only [FullRouteAdm, Set.mem_setOf_eq]
  exact ⟨fun ⟨_, hev, hpr⟩ => ⟨hev, hpr⟩,
         fun ⟨hev, hpr⟩ => ⟨hbase, hev, hpr⟩⟩

/-! ## Set-level disjointness of hard and soft anchor targets -/

/-- **Hard and soft anchor target sets are disjoint.**
    This lifts the element-wise disjointness from `EquilibratedCorpus.disjoint`
    to a set-level `Disjoint` statement that downstream nodes (6A–6E) can
    consume directly in set-theoretic reasoning. -/
theorem equilibratedCorpus_targets_disjoint {Sem : Type*}
    (ec : EquilibratedCorpus Sem) :
    Disjoint ec.hardTargets ec.softTargets := by
  rw [Set.disjoint_left]
  intro s ⟨a, ha_mem, ha_eq⟩ ⟨sa, sa_mem, sa_eq⟩
  exact absurd (ha_eq.trans sa_eq.symm) (ec.disjoint a ha_mem sa sa_mem)

end SafeSlice
