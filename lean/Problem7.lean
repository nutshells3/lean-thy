import Mathlib
import Problem6

noncomputable section

namespace SafeSlice

/-!
# Problem 7

This file formalizes orchestration objects over Deploy(G, M), including role
placement, escalation, workflow feasibility predicates, and the explicit
optimization target that 4D should realize.
-/

/-! ## Orchestration carrier types -/

/-- A **role** in the orchestration: each role is backed by a proposer and
    an admissibility regime, so it carries its own deployable envelope. -/
structure Role (Sem : Type*) where
  /-- Human-readable identifier for the role. -/
  name : String
  /-- The proposer (generator) backing this role. -/
  proposer : Proposer Sem
  /-- The admissibility regime governing this role. -/
  regime : AdmRegime Sem
  /-- Interaction cost: how many interactions this role requires per semantic
      object (e.g. LLM calls). Used to enforce interaction-budget constraints. -/
  interactionCost : Sem → NNReal
  /-- Monetary/resource cost per semantic object for this role. Used to
      enforce per-task cost-budget constraints. -/
  costMeasure : Sem → NNReal

/-- The deployable envelope of a role is `Deploy(G, M)` for that role's
    proposer and regime. -/
def Role.deployable {Sem : Type*} (r : Role Sem) : Set Sem :=
  Deploy r.proposer r.regime

/-- A **task** is a semantic obligation that must be covered by a role. -/
structure Task (Sem : Type*) where
  /-- The semantic object this task requires to be deployable. -/
  target : Sem
  /-- Maximum interaction budget (e.g. LLM calls) allowed for this task. -/
  interactionBudget : NNReal
  /-- Maximum cost budget for this task. -/
  costBudget : NNReal

/-- A **task plan**: a finite collection of tasks that must all be covered. -/
structure TaskPlan (Sem : Type*) where
  /-- The tasks in this plan. -/
  tasks : Finset (Task Sem)

/-- A **role placement**: assigns each task in a plan to a role. -/
structure RolePlacement (Sem : Type*) where
  /-- The task plan being placed. -/
  plan : TaskPlan Sem
  /-- Available roles. -/
  roles : Finset (Role Sem)
  /-- Assignment function: maps each task to a role. -/
  assign : Task Sem → Role Sem
  /-- Every assigned role is drawn from the available roles. -/
  assign_mem : ∀ t ∈ plan.tasks, assign t ∈ roles

/-- An **escalation policy**: specifies when and how to escalate a task
    from one role to another (e.g. from cheapJudge to human). -/
structure EscalationPolicy (Sem : Type*) where
  /-- The available roles (same pool as the placement). -/
  roles : Finset (Role Sem)
  /-- Escalation function: given a task and the current role, returns
      the escalation target role (or the same role if no escalation). -/
  escalate : Task Sem → Role Sem → Role Sem
  /-- The escalation target is always in the role pool. -/
  escalate_mem : ∀ t r, r ∈ roles → escalate t r ∈ roles

/-! ## Orchestration predicates -/

/-- A role **covers** a task when the task's target is in the role's
    deployable envelope. -/
def Role.covers {Sem : Type*} (r : Role Sem) (t : Task Sem) : Prop :=
  t.target ∈ r.deployable

/-- A role placement is **deploy-sound** when every task is covered by its
    assigned role — i.e., the task target lies in `Deploy(G, M)` for that
    role's proposer and regime. -/
def RolePlacement.deploySound {Sem : Type*} (rp : RolePlacement Sem) : Prop :=
  ∀ t ∈ rp.plan.tasks, (rp.assign t).covers t

/-- A role placement is **cost-feasible** when no task exceeds its per-task
    cost budget given the assigned role's cost measure. -/
def RolePlacement.costFeasible {Sem : Type*} (rp : RolePlacement Sem) : Prop :=
  ∀ t ∈ rp.plan.tasks,
    (rp.assign t).costMeasure t.target ≤ t.costBudget

/-- A role placement is **risk-feasible** when every task's risk (under the
    assigned role's regime) stays within the regime's own risk bound. -/
def RolePlacement.riskFeasible {Sem : Type*} (rp : RolePlacement Sem) : Prop :=
  ∀ t ∈ rp.plan.tasks,
    (rp.assign t).regime.riskMeasure t.target ≤ (rp.assign t).regime.riskBound

/-- A role placement is **interaction-feasible** when no task exceeds its
    interaction budget given the assigned role's interaction cost. -/
def RolePlacement.interactionFeasible {Sem : Type*} (rp : RolePlacement Sem) : Prop :=
  ∀ t ∈ rp.plan.tasks,
    (rp.assign t).interactionCost t.target ≤ t.interactionBudget

/-- An escalation policy is **sound** when, for every task and its current
    assigned role, escalation preserves coverage: if the current role covers
    the task, the escalation target also covers it. -/
def EscalationPolicy.sound {Sem : Type*}
    (ep : EscalationPolicy Sem) (rp : RolePlacement Sem) : Prop :=
  ∀ t ∈ rp.plan.tasks,
    let r := rp.assign t
    r ∈ ep.roles →
    r.covers t →
    (ep.escalate t r).covers t

/-- An escalation policy **weakly improves** risk: escalation never increases
    the risk measure for the task's target. -/
def EscalationPolicy.riskImproving {Sem : Type*}
    (ep : EscalationPolicy Sem) (rp : RolePlacement Sem) : Prop :=
  ∀ t ∈ rp.plan.tasks,
    let r := rp.assign t
    r ∈ ep.roles →
    (ep.escalate t r).regime.riskMeasure t.target ≤
      r.regime.riskMeasure t.target

/-! ## Workflow: composite orchestration object -/

/-- A **workflow** bundles a task plan, role placement, and escalation policy
    into a single orchestration object. -/
structure Workflow (Sem : Type*) where
  /-- The underlying role placement. -/
  placement : RolePlacement Sem
  /-- The escalation policy. -/
  escalation : EscalationPolicy Sem
  /-- Global risk budget for the workflow. -/
  riskBudget : NNReal
  /-- Global cost budget for the workflow. -/
  costBudget : NNReal

/-- A workflow is feasible when its placement and escalation predicates all hold. -/
def Workflow.feasible {Sem : Type*} (w : Workflow Sem) : Prop :=
  w.placement.deploySound ∧
  w.placement.costFeasible ∧
  w.placement.riskFeasible ∧
  w.placement.interactionFeasible ∧
  w.escalation.sound w.placement ∧
  w.escalation.riskImproving w.placement

/-! ## Explicit deployment optimum target

The main 4D target is not only a local swap-style near-minimality statement.
Once Problem 6 has fixed the exact `Deploy(G, M)` surface, the first
orchestration theorem should assert existence of a budget-feasible objective
optimum on an explicit finite candidate carrier inside that deployable set.
The typed workflow objects below should later refine a witness of that theorem.
-/

/-- `s` is objective-optimal among budget-feasible candidates. -/
def OptimalOnCandidates {Sem : Type*} [DecidableEq Sem]
    (cands : Finset Sem) (cost objective : Sem → NNReal) (budget : NNReal)
    (s : Sem) : Prop :=
  s ∈ cands ∧
  cost s ≤ budget ∧
  ∀ s', s' ∈ cands → cost s' ≤ budget → objective s ≤ objective s'

/-- Specification alias for the finite-carrier optimum claim. The actual 4D
    capstone is the theorem `deploy_optimal_exists` below. -/
def DeployOptimalExists {Sem : Type*} [DecidableEq Sem]
    (G : Proposer Sem) (M : AdmRegime Sem) (cands : Finset Sem)
    (cost objective : Sem → NNReal) (budget : NNReal) : Prop :=
  (∀ s ∈ cands, s ∈ Deploy G M) →
  (∃ s ∈ cands, cost s ≤ budget) →
  ∃ s, OptimalOnCandidates cands cost objective budget s

/-! ## Orchestration feasibility theorem -/
/-- On any finite candidate carrier inside `Deploy(G, M)`, a budget-feasible
    objective optimum exists. This is the actual 4D capstone theorem, rather
    than only a named proposition. -/
theorem deploy_optimal_exists {Sem : Type*} [DecidableEq Sem]
    (G : Proposer Sem) (M : AdmRegime Sem)
    (cands : Finset Sem)
    (cost objective : Sem → NNReal)
    (budget : NNReal)
    (hcands : ∀ s ∈ cands, s ∈ Deploy G M)
    (hfeas : ∃ s ∈ cands, cost s ≤ budget) :
    ∃ s, s ∈ Deploy G M ∧ OptimalOnCandidates cands cost objective budget s := by
  let feasible := cands.filter fun s => cost s ≤ budget
  have hfeasible : feasible.Nonempty := by
    rcases hfeas with ⟨s, hsCands, hsBudget⟩
    refine ⟨s, ?_⟩
    simp only [feasible, Finset.mem_filter, hsCands, hsBudget, and_self]
  rcases Finset.exists_min_image feasible objective hfeasible with ⟨s, hsFeasible, hsMin⟩
  have hsCandsBudget : s ∈ cands ∧ cost s ≤ budget := by
    simpa only [feasible, Finset.mem_filter] using hsFeasible
  refine ⟨s, hcands s hsCandsBudget.1, hsCandsBudget.1, hsCandsBudget.2, ?_⟩
  intro s' hs' hsBudget'
  exact hsMin s' (by simpa only [feasible, Finset.mem_filter] using And.intro hs' hsBudget')

/-- The feasibility assumptions assemble into Workflow.feasible. -/
theorem orchestration_feasibility {Sem : Type*} (w : Workflow Sem)
    (h_sound : w.placement.deploySound)
    (h_cost : w.placement.costFeasible)
    (h_risk : w.placement.riskFeasible)
    (h_interaction : w.placement.interactionFeasible)
    (h_esc_sound : w.escalation.sound w.placement)
    (h_esc_risk : w.escalation.riskImproving w.placement) :
    w.feasible :=
  ⟨h_sound, h_cost, h_risk, h_interaction, h_esc_sound, h_esc_risk⟩

/-! ## Connecting orchestration to Deploy(G, M)

This section restates deploy-soundness using the Deploy(G, M) decomposition.
-/

/-- Deploy-soundness unpacks to the intersection characterization:
    every task target is both reachable by the role's proposer and
    admissible under the role's regime. -/
theorem deploySound_characterize {Sem : Type*} (rp : RolePlacement Sem)
    (h : rp.deploySound) (t : Task Sem) (ht : t ∈ rp.plan.tasks) :
    t.target ∈ Reach (rp.assign t).proposer ∧
    t.target ∈ Adm (rp.assign t).regime := by
  have := h t ht
  simp only [Role.covers, Role.deployable, Deploy, Set.mem_inter_iff] at this
  exact this

/-- **Generator-invariance lifts to orchestration**: replacing a role's proposer
    with one that has the same reach preserves deploy-soundness. -/
theorem deploySound_generator_invariant {Sem : Type*}
    (rp : RolePlacement Sem)
    (r_old r_new : Role Sem)
    (hreach : Reach r_old.proposer = Reach r_new.proposer)
    (hregime : r_old.regime = r_new.regime)
    (h : rp.deploySound)
    (_hassign : ∀ t ∈ rp.plan.tasks, rp.assign t = r_old → True) :
    ∀ t ∈ rp.plan.tasks,
      rp.assign t = r_old →
      t.target ∈ Deploy r_new.proposer r_new.regime := by
  intro t ht hrole
  have hds := h t ht
  simp only [Role.covers, Role.deployable, hrole] at hds
  rw [← deploy_generator_invariant r_old.proposer r_new.proposer _ hreach,
      ← hregime]
  exact hds

/-- **Conservative-upgrade lifts to orchestration**: if a role's proposer is
    upgraded to reach more semantics (under fixed regime), deploy-soundness
    is preserved. -/
theorem deploySound_conservative_upgrade {Sem : Type*}
    (rp : RolePlacement Sem)
    (r_old r_new : Role Sem)
    (hexp : Reach r_old.proposer ⊆ Reach r_new.proposer)
    (hregime : r_old.regime = r_new.regime)
    (h : rp.deploySound) :
    ∀ t ∈ rp.plan.tasks,
      rp.assign t = r_old →
      t.target ∈ Deploy r_new.proposer r_new.regime := by
  intro t ht hrole
  have hds := h t ht
  simp only [Role.covers, Role.deployable, hrole] at hds
  rw [← hregime]
  exact deploy_conservative_upgrade r_old.proposer r_new.proposer
    r_old.regime hexp hds

/-! ## Workflow realizes the deployment optimum

The typed orchestration objects (TaskPlan, RolePlacement, EscalationPolicy,
Workflow) are linked to `deploy_optimal_exists` as refinements: a feasible
workflow's task targets form the finite candidate carrier inside Deploy(G, M),
and the workflow's cost structure provides the budget-feasibility witness.
-/

/-- Extract the finite set of task targets from a task plan. -/
def TaskPlan.targetSet {Sem : Type*} [DecidableEq Sem]
    (plan : TaskPlan Sem) : Finset Sem :=
  plan.tasks.image Task.target

/-- A feasible workflow's task targets all lie in `Deploy(G, M)` for their
    assigned role's proposer and regime. This extracts the Deploy-membership
    certificates from deploy-soundness for every task target. -/
theorem Workflow.targets_in_deploy {Sem : Type*}
    (w : Workflow Sem) (hfeas : w.feasible) :
    ∀ t ∈ w.placement.plan.tasks,
      t.target ∈ Deploy (w.placement.assign t).proposer
                        (w.placement.assign t).regime := by
  intro t ht
  exact hfeas.1 t ht

/-- **Workflow realizes the deployment optimum**: given a feasible workflow
    whose roles share a common proposer `G` and regime `M`, and a nonempty
    task plan, the workflow's task targets form a finite carrier inside
    `Deploy(G, M)` on which a budget-feasible objective optimum exists.
    This formally links the typed orchestration objects to `deploy_optimal_exists`. -/
theorem workflow_realizes_optimum {Sem : Type*} [DecidableEq Sem]
    (w : Workflow Sem)
    (G : Proposer Sem) (M : AdmRegime Sem)
    (objective : Sem → NNReal)
    (budget : NNReal)
    (hfeas : w.feasible)
    (huniform : ∀ t ∈ w.placement.plan.tasks,
      (w.placement.assign t).proposer = G ∧
      (w.placement.assign t).regime = M)
    (cost : Sem → NNReal)
    (hne : ∃ t ∈ w.placement.plan.tasks, cost t.target ≤ budget) :
    ∃ s, s ∈ Deploy G M ∧
      OptimalOnCandidates w.placement.plan.targetSet
        cost objective budget s := by
  have hcands : ∀ s ∈ w.placement.plan.targetSet, s ∈ Deploy G M := by
    intro s hs
    simp only [TaskPlan.targetSet, Finset.mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    have := hfeas.1 t ht
    have ⟨hG, hM⟩ := huniform t ht
    simp only [Role.covers, Role.deployable, hG, hM] at this
    exact this
  have hfeasBudget : ∃ s ∈ w.placement.plan.targetSet, cost s ≤ budget := by
    rcases hne with ⟨t, ht, hle⟩
    exact ⟨t.target, Finset.mem_image_of_mem _ ht, hle⟩
  exact deploy_optimal_exists G M w.placement.plan.targetSet
    cost objective budget hcands hfeasBudget

/-- **Workflow-synthesis target**: a feasible workflow with a common
    proposer/regime and a nonempty budget-feasible task witnesses the
    `DeployOptimalExists` specification. -/
theorem workflow_witnesses_deploy_optimal {Sem : Type*} [DecidableEq Sem]
    (w : Workflow Sem)
    (G : Proposer Sem) (M : AdmRegime Sem)
    (objective : Sem → NNReal)
    (budget : NNReal)
    (hfeas : w.feasible)
    (huniform : ∀ t ∈ w.placement.plan.tasks,
      (w.placement.assign t).proposer = G ∧
      (w.placement.assign t).regime = M)
    (cost : Sem → NNReal)
    (hne : ∃ t ∈ w.placement.plan.tasks, cost t.target ≤ budget) :
    DeployOptimalExists G M w.placement.plan.targetSet
      cost objective budget := by
  intro hcands hfeasBudget
  rcases workflow_realizes_optimum w G M objective budget hfeas huniform
    cost hne with ⟨s, _, hopt⟩
  exact ⟨s, hopt⟩

/-! ## Local near-minimality precursor

This section defines a weaker single-role swap predicate. It is useful local
structure, but the roadmap target above is the finite-carrier optimum-existence
theorem over the exact `Deploy(G, M)` envelope. Near-minimality is a corollary
or approximation layer, not the main headline.
-/

/-- A workflow is near-minimal when no cheaper covering single-role swap exists. -/
def Workflow.nearMinimal {Sem : Type*} (w : Workflow Sem) : Prop :=
  ∀ t ∈ w.placement.plan.tasks,
  ∀ r' ∈ w.placement.roles,
    r'.covers t →
    r'.costMeasure t.target ≤
      (w.placement.assign t).costMeasure t.target →
    (w.placement.assign t).costMeasure t.target ≤
      r'.costMeasure t.target

/-- A near-minimal workflow admits no strictly cheaper covering single-role swap. -/
theorem nearMinimal_no_strict_improvement {Sem : Type*} (w : Workflow Sem)
    (_hfeas : w.feasible)
    (hmin : w.nearMinimal) :
    ∀ t ∈ w.placement.plan.tasks,
    ∀ r' ∈ w.placement.roles,
      r'.covers t →
      r'.costMeasure t.target ≤
        (w.placement.assign t).costMeasure t.target →
      (w.placement.assign t).costMeasure t.target =
        r'.costMeasure t.target := by
  intro t ht r' hr' hcov hle
  exact le_antisymm (hmin t ht r' hr' hcov hle) hle

end SafeSlice
