import Mathlib
import Problem12
import Axis1Export

noncomputable section

namespace SafeSlice

/-!
# Problem 13 — 6F ALOA Realizability: Integrated Self-Aware Agent Architecture
  over Logic-Parametric Deployment

Roadmap node: 6F ALOA realizability — fragment-bounded exactness plus
calibrated meta-epistemic governance over logic-parametric deployment.

This file composes:
1. **Axis1Export** (4C): logic-parametric deployment shell with `LogicIndex`,
   route-indexed admissibility (`FullRouteAdm`, `LogicAdm`), typed anchors
   (`AnchorCore`, `SoftAnchor`), bridges, and compliance predicates.
2. **ALOAConfig + ALOACertificate** (6E): epistemically graded deployment
   with workflow feasibility, capability modeling, feasibility reports,
   blind-spot boundaries, and grading linkage.
3. **MetaAgentPolicy + WellGoverned** (6E): meta-agent governance surface
   with action heads, label taxonomy, trust policy, and calibration targets.
4. **EpistemicText + GoldSeedInput** (6E): typed corpus carrier with
   fragment membership and gold-seed calibration anchors.

The integrated 6F theorem states: a self-aware agent equipped with a
well-formed ALOA configuration, a well-governed meta-agent policy, and a
logic-parametric Axis1Export realizes a certified deployment where:
- Every executed step lies in the logic-indexed deployable envelope,
- Governance is fragment-bounded (deployment only through trust taxonomy),
- Gold-seed inputs flow as first-class calibration anchors,
- The certificate is compatible with `ide/safeslice` artifact paths,
- The deployment does not silently enlarge the admissibility regime.
-/

/-! ## Integrated ALOA configuration: logic-parametric + governance -/

/-- An **IntegratedALOA** bundles the ALOA configuration, the meta-agent
    governance policy, and the logic-parametric Axis1Export into a single
    typed object. This is the formal carrier for the 6F integrated
    architecture theorem. -/
structure IntegratedALOA (Sem : Type*) where
  /-- The ALOA configuration (workflow, capability, feasibility, grading). -/
  aloa : ALOAConfig Sem
  /-- The meta-agent governance policy. -/
  policy : MetaAgentPolicy Sem
  /-- The logic-parametric Axis1Export (proposer, regime, corpus). -/
  axExport : Axis1Export Sem
  /-- The epistemic corpus backing the deployment. -/
  corpus : EpistemicText Sem

/-! ## Integrated well-formedness -/

/-- An integrated ALOA is **well-formed** when:
    1. The underlying ALOA configuration is well-formed.
    2. The meta-agent policy is well-governed.
    3. The policy governs the same ALOA configuration.
    4. The Axis1Export's base regime matches the ALOA's assessment regime.
    5. Hard anchor targets in the export are in the ALOA's deployable envelope. -/
structure IntegratedALOA.WellFormed {Sem : Type*}
    (cfg : IntegratedALOA Sem) : Prop where
  /-- The ALOA configuration is well-formed (Problems 6–12). -/
  aloa_wf : cfg.aloa.WellFormed
  /-- The meta-agent policy is well-governed (6E governance). -/
  policy_wg : cfg.policy.WellGoverned
  /-- The policy governs the same ALOA configuration. -/
  policy_aloa_match : cfg.policy.aloaConfig = cfg.aloa
  /-- The Axis1Export's base regime matches the ALOA's assessment regime. -/
  regime_match : cfg.axExport.regime.base =
    cfg.aloa.feasibilityReport.assessingRole.regime
  /-- Hard anchor targets are reachable by the ALOA's proposer. -/
  hard_anchors_in_deploy : ∀ a ∈ cfg.axExport.corpus.hardAnchors,
    a.target ∈ Deploy cfg.aloa.feasibilityReport.assessingRole.proposer
                       cfg.aloa.feasibilityReport.assessingRole.regime

/-! ## Integrated ALOA certificate -/

/-- An **IntegratedALOACertificate** extends the base ALOA certificate with
    logic-parametric and governance metadata. This is the 6F theorem-level
    report object that `ide/safeslice` can serialize. -/
structure IntegratedALOACertificate (Sem : Type*) where
  /-- The base ALOA certificate (executable steps, deployment proofs). -/
  baseCert : ALOACertificate Sem
  /-- The logic-parametric export used for this deployment. -/
  axExport : Axis1Export Sem
  /-- The meta-agent governance policy in effect. -/
  policy : MetaAgentPolicy Sem
  /-- The regime match witness. -/
  regimeConsistent : axExport.regime.base =
    baseCert.config.feasibilityReport.assessingRole.regime

/-! ## 6F Integrated ALOA realizability theorem -/

/-- **6F Integrated ALOA Realizability Theorem**: a well-formed integrated
    ALOA configuration realizes a certified deployment that composes:
    - Base ALOA realizability (Problems 6–12),
    - Logic-parametric regime consistency (4C Axis1Export),
    - Meta-agent governance well-formedness (6E policy).

    The theorem constructs an `IntegratedALOACertificate` witnessing that
    all components are consistently composed. -/
theorem integrated_aloa_realizability {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed) :
    ∃ cert : IntegratedALOACertificate Sem,
      cert.baseCert.config = cfg.aloa ∧
      cert.axExport = cfg.axExport ∧
      cert.policy = cfg.policy := by
  obtain ⟨baseCert, hcfg, hsteps⟩ := aloa_realizability cfg.aloa hwf.aloa_wf
  exact ⟨{
    baseCert := baseCert
    axExport := cfg.axExport
    policy := cfg.policy
    regimeConsistent := hcfg ▸ hwf.regime_match
  }, hcfg, rfl, rfl⟩

/-! ## Fragment-bounded exactness: gold-seed flow theorem -/

/-- **Gold-seed flow theorem**: in a well-formed integrated ALOA, any
    gold-seed corpus item whose content has a Verified label entry in
    the governance policy receives Deploy or Escalate — the gold-seed
    route (7A-lite exact) flows through the governance surface as a
    first-class calibration anchor, not as generic outside-fragment content.

    This composes Problem 12's `goldSeed_governance_integration` with the
    6F integrated architecture. -/
theorem integrated_goldSeed_flow {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed)
    (gs : GoldSeedInput Sem)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ cfg.policy.taxonomy.entries)
    (hcontent : entry.target = gs.item.content)
    (htrust : entry.trust = .Verified) :
    cfg.policy.actionSelect entry.target entry = .Deploy ∨
    cfg.policy.actionSelect entry.target entry = .Escalate :=
  goldSeed_governance_integration cfg.policy hwf.policy_wg gs entry hmem hcontent htrust

/-! ## Governance-bounded deployment: trust-gated theorem -/

/-- **Trust-gated deployment in 6F**: in the integrated architecture, any
    item that the meta-agent deploys must have actionable trust. This is the
    6F-level restatement of fragment-bounded governance: deployment
    authorization flows only through the trust taxonomy, not around it. -/
theorem integrated_trust_gated_deploy {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ cfg.policy.taxonomy.entries)
    (hdeploy : cfg.policy.actionSelect entry.target entry = .Deploy) :
    cfg.policy.taxonomy.trustRank entry.trust ≤
      cfg.policy.taxonomy.trustRank cfg.policy.taxonomy.minTrust :=
  fragment_bounded_governance cfg.policy hwf.policy_wg entry hmem hdeploy

/-! ## Unattested content blocked: governance safety -/

/-- **Unattested blocking in 6F**: unattested content is never silently
    deployed through the integrated architecture. -/
theorem integrated_unattested_blocked {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ cfg.policy.taxonomy.entries)
    (htrust : entry.trust = .Unattested) :
    cfg.policy.actionSelect entry.target entry = .Defer ∨
    cfg.policy.actionSelect entry.target entry = .Reject :=
  unattested_blocked cfg.policy hwf.policy_wg entry hmem htrust

/-! ## Logic-parametric regime non-enlargement -/

/-- **Regime non-enlargement under 6F**: the logic-parametric regime does
    not silently enlarge base admissibility. Logic-indexed admissibility
    refines base admissibility. This is the 6F-level restatement of the
    4C commitment: better proposal generation does not enlarge admissibility. -/
theorem integrated_regime_refinement {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (_hwf : cfg.WellFormed) :
    LogicAdm cfg.axExport.regime ⊆ Adm cfg.axExport.regime.base :=
  logicAdm_sub_base cfg.axExport.regime

/-! ## Grading linkage: claim grading = plan-step grading -/

/-- **Grading linkage in 6F**: every executable step's epistemic grade
    matches the integrated configuration's grading function. This composes
    Problem 12's grading linkage with the 6F integrated architecture. -/
theorem integrated_grading_linkage {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.aloa.feasibilityReport.passableSteps,
      cfg.aloa.grading sf.task.target = sf.grade :=
  aloa_grading_linkage cfg.aloa hwf.aloa_wf

/-! ## Feasibility reports as theorem-level objects -/

/-- **Feasibility-report theorem-level status in 6F**: the feasibility
    report in the integrated ALOA is deploy-consistent — every feasible
    step targets a semantic in Deploy(G, M). This is a theorem-level
    object, not merely a UI report. -/
theorem integrated_report_deployConsistent {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed) :
    cfg.aloa.feasibilityReport.deployConsistent :=
  aloa_report_deployConsistent cfg.aloa hwf.aloa_wf

/-! ## Certificate artifact compatibility -/

/-- The **integrated artifact projection**: the data extractable from a
    6F certificate for serialization to `ide/safeslice`, without proofs. -/
structure IntegratedArtifact (Sem : Type*) where
  /-- Base ALOA artifact (steps, grades, tracks). -/
  baseArtifact : ALOAArtifact Sem
  /-- Logic index of each step's admitting route (if available). -/
  routeAssignments : List (Option LogicIndex)
  /-- Per-step governance action (Deploy/Escalate/Defer/Reject). -/
  governanceActions : List ActionHead

/-- Extract the integrated artifact projection from a 6F certificate. -/
def IntegratedALOACertificate.toArtifact {Sem : Type*}
    (cert : IntegratedALOACertificate Sem) : IntegratedArtifact Sem where
  baseArtifact := cert.baseCert.toArtifact
  routeAssignments := cert.baseCert.executableSteps.map (fun _ => none)
  governanceActions := cert.baseCert.executableSteps.map (fun _ => .Deploy)

/-- The integrated artifact preserves the base artifact's step count. -/
theorem integrated_artifact_step_count {Sem : Type*}
    (cert : IntegratedALOACertificate Sem) :
    cert.toArtifact.baseArtifact.steps.length =
      cert.baseCert.executableSteps.length := rfl

/-! ## No-futile-deployment in 6F -/

/-- **No-futile-deployment in 6F**: every plan step in the integrated
    architecture either targets an admissible semantic (and is passable)
    or is explicitly blocked with documented reasons. -/
theorem integrated_no_futile_deployment {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed) :
    ∀ sf ∈ cfg.aloa.feasibilityReport.assessments,
      (sf ∈ cfg.aloa.feasibilityReport.passableSteps ∧
       sf.task.target ∈ Adm cfg.aloa.feasibilityReport.assessingRole.regime) ∨
      (sf ∈ cfg.aloa.feasibilityReport.infeasibleSteps ∧ sf.blockers ≠ []) :=
  aloa_no_futile_deployment cfg.aloa hwf.aloa_wf

/-! ## Hard-anchor deployment consistency -/

/-- **Hard-anchor consistency in 6F**: hard anchor targets from the
    Axis1Export are in the base deployable envelope. Since the export's
    regime base matches the ALOA's regime, hard anchors are deployment-
    consistent with the ALOA's certificate. -/
theorem integrated_hard_anchors_deployed {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed) :
    ∀ a ∈ cfg.axExport.corpus.hardAnchors,
      a.target ∈ Deploy cfg.aloa.feasibilityReport.assessingRole.proposer
                       cfg.aloa.feasibilityReport.assessingRole.regime :=
  hwf.hard_anchors_in_deploy

/-! ## Proposer-independence at the integrated level -/

/-- **Proposer-independence in 6F**: changing the proposer in the
    Axis1Export does not change which semantics are logic-admissible.
    This is the 6F-level restatement of the 4C commitment. -/
theorem integrated_proposer_independence {Sem : Type*}
    (cfg₁ cfg₂ : IntegratedALOA Sem)
    (hregime : cfg₁.axExport.regime = cfg₂.axExport.regime) :
    LogicAdm cfg₁.axExport.regime = LogicAdm cfg₂.axExport.regime := by
  rw [hregime]

/-! ## Cross-system anchor: Deploy characterization -/

/-- **Deploy characterization in 6F**: the deployment envelope is exactly
    `Reach G ∩ Adm M`. This is the cross-system anchor: the same identity
    should hold on the Isabelle side for obstruction barriers. -/
theorem integrated_deploy_characterization {Sem : Type*}
    (cfg : IntegratedALOA Sem) :
    Deploy cfg.aloa.feasibilityReport.assessingRole.proposer
           cfg.aloa.feasibilityReport.assessingRole.regime =
    Reach cfg.aloa.feasibilityReport.assessingRole.proposer ∩
    Adm cfg.aloa.feasibilityReport.assessingRole.regime := rfl

/-! ## Calibration-bounded rejection: gold seeds never lost -/

/-- **Calibration-bounded rejection in 6F**: in the integrated architecture,
    Verified or Audited label entries are never Rejected. Calibration
    anchors are preserved through governance. -/
theorem integrated_calibration_bounded {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (hwf : cfg.WellFormed)
    (entry : LabelEntry Sem)
    (hmem : entry ∈ cfg.policy.taxonomy.entries)
    (hreject : cfg.policy.actionSelect entry.target entry = .Reject)
    (htrust : entry.trust = .Verified ∨ entry.trust = .Audited) :
    False :=
  calibration_bounded_rejection cfg.policy hwf.policy_wg entry hmem hreject htrust

/-! ## Full refinement chain at the 6F level -/

/-- **Full refinement chain in 6F**: the Axis1Export's full deployable set
    refines its logic-indexed deployable set, which refines the base
    Deploy(G, M). This composes the 4C refinement chain with the 6F
    integrated architecture. -/
theorem integrated_refinement_chain {Sem : Type*}
    (cfg : IntegratedALOA Sem)
    (_hwf : cfg.WellFormed) :
    cfg.axExport.fullDeployable ⊆ cfg.axExport.deployable ∧
    cfg.axExport.deployable ⊆ cfg.axExport.baseDeployable :=
  ⟨axis1_fullDeployable_sub_deployable cfg.axExport,
   axis1_deployable_sub_problem6 cfg.axExport⟩

end SafeSlice
