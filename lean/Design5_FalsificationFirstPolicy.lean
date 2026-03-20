import Design4_VarianceAdaptiveStoppingPolicy

noncomputable section

namespace SafeSlice

/-!
# Design 5: Falsification-First Policy
-/

inductive DesignDecision where
  | accept
  | reject
  | defer
  deriving DecidableEq, Repr

structure DesignDecisionProblem (Action Evidence : Type*) [DecidableEq Action] where
  actions : Finset Action
  utility : Action → Evidence → ℝ
  cost : Action → Evidence → ℝ

structure DesignStagedPolicy (Action Evidence : Type*) where
  refuteCost : ℝ
  confirmCost : ℝ
  refuteTest : Action → Evidence → Bool
  confirmTest : Action → Evidence → Bool

def designSurvivors {Action Evidence : Type*}
    (policy : DesignStagedPolicy Action Evidence) (candidates : Finset Action)
    (evidence : Evidence) : Finset Action :=
  candidates.filter fun action => policy.refuteTest action evidence

def designCertified {Action Evidence : Type*}
    (policy : DesignStagedPolicy Action Evidence) (candidates : Finset Action)
    (evidence : Evidence) : Finset Action :=
  (designSurvivors policy candidates evidence).filter
    fun action => policy.confirmTest action evidence

def designDecisionGap {Action Evidence : Type*} [DecidableEq Action]
    (problem : DesignDecisionProblem Action Evidence) (evidence : Evidence)
    (action action' : Action) : ℝ :=
  (problem.utility action evidence - problem.cost action evidence) -
    (problem.utility action' evidence - problem.cost action' evidence)

def designDecisionCertificate {Action Evidence : Type*} [DecidableEq Action]
    (problem : DesignDecisionProblem Action Evidence) (evidence : Evidence)
    (action : Action) (certify : Action → Prop) (delta : ℝ) : Prop :=
  action ∈ problem.actions ∧
    certify action ∧
    ∀ action' ∈ problem.actions, -delta ≤ designDecisionGap problem evidence action action'

def designRefutationSound {Action Evidence : Type*} [DecidableEq Action]
    (policy : DesignStagedPolicy Action Evidence)
    (problem : DesignDecisionProblem Action Evidence) (evidence : Evidence) : Prop :=
  ∀ action ∈ problem.actions, policy.refuteTest action evidence = true

def designConfirmationSound {Action Evidence : Type*} [DecidableEq Action]
    (policy : DesignStagedPolicy Action Evidence)
    (problem : DesignDecisionProblem Action Evidence) (evidence : Evidence) (delta : ℝ) : Prop :=
  ∀ action ∈ problem.actions,
    policy.confirmTest action evidence = true →
      ∀ action' ∈ problem.actions,
        -delta ≤ designDecisionGap problem evidence action action'

def designStagedBudget {Action Evidence : Type*}
    (policy : DesignStagedPolicy Action Evidence) (candidates : Finset Action)
    (evidence : Evidence) : ℝ :=
  (candidates.card : ℝ) * policy.refuteCost +
    ((designSurvivors policy candidates evidence).card : ℝ) * policy.confirmCost

theorem designStagedBudgetSaving {Action Evidence : Type*}
    (policy : DesignStagedPolicy Action Evidence) (candidates : Finset Action)
    (evidence : Evidence) (hConfirm : 0 < policy.confirmCost)
    (_hRefute : 0 ≤ policy.refuteCost)
    (hStrict : (designSurvivors policy candidates evidence).card < candidates.card) :
    designStagedBudget policy candidates evidence <
      (candidates.card : ℝ) * policy.confirmCost +
        (candidates.card : ℝ) * policy.refuteCost := by
  have hCard : ((designSurvivors policy candidates evidence).card : ℝ) < candidates.card := by
    exact_mod_cast hStrict
  have hConfirmPart :
      ((designSurvivors policy candidates evidence).card : ℝ) * policy.confirmCost <
        (candidates.card : ℝ) * policy.confirmCost := by
    exact mul_lt_mul_of_pos_right hCard hConfirm
  dsimp [designStagedBudget]
  linarith

theorem designDecisionFocusedGuarantee {Action Evidence : Type*} [DecidableEq Action]
    {policy : DesignStagedPolicy Action Evidence}
    {problem : DesignDecisionProblem Action Evidence} {evidence : Evidence}
    {actionStar : Action}
    (hMem : actionStar ∈ problem.actions)
    (hRefute : designRefutationSound policy problem evidence) :
    actionStar ∈ designSurvivors policy problem.actions evidence := by
  have hKeep : policy.refuteTest actionStar evidence = true :=
    hRefute actionStar hMem
  simp [designSurvivors, hMem, hKeep]

theorem designCertifiedNearOptimal {Action Evidence : Type*} [DecidableEq Action]
    {policy : DesignStagedPolicy Action Evidence}
    {problem : DesignDecisionProblem Action Evidence} {evidence : Evidence}
    {action action' : Action} {delta : ℝ}
    (hConfirm : designConfirmationSound policy problem evidence delta)
    (hCertified : action ∈ designCertified policy problem.actions evidence)
    (hMem : action' ∈ problem.actions) :
    -delta ≤ designDecisionGap problem evidence action action' := by
  have hCertifiedMem :
      action ∈ designSurvivors policy problem.actions evidence ∧
        policy.confirmTest action evidence = true := by
    simpa [designCertified] using Finset.mem_filter.mp hCertified
  have hSurvivorMem :
      action ∈ problem.actions ∧ policy.refuteTest action evidence = true := by
    simpa [designSurvivors] using Finset.mem_filter.mp hCertifiedMem.1
  exact hConfirm action hSurvivorMem.1 hCertifiedMem.2 action' hMem

theorem designStagedPolicyInstantiatesCertificate {Action Evidence : Type*} [DecidableEq Action]
    {policy : DesignStagedPolicy Action Evidence}
    {problem : DesignDecisionProblem Action Evidence} {evidence : Evidence}
    {action : Action} {delta : ℝ}
    (hConfirm : designConfirmationSound policy problem evidence delta)
    (hCertified : action ∈ designCertified policy problem.actions evidence) :
    designDecisionCertificate problem evidence action
      (fun candidate => candidate ∈ designCertified policy problem.actions evidence) delta := by
  have hCertifiedMem :
      action ∈ designSurvivors policy problem.actions evidence ∧
        policy.confirmTest action evidence = true := by
    simpa [designCertified] using Finset.mem_filter.mp hCertified
  have hSurvivorMem :
      action ∈ problem.actions ∧ policy.refuteTest action evidence = true := by
    simpa [designSurvivors] using Finset.mem_filter.mp hCertifiedMem.1
  refine ⟨hSurvivorMem.1, hCertified, ?_⟩
  intro action' hMem
  exact designCertifiedNearOptimal hConfirm hCertified hMem

theorem designStagedCertificationSummary {Action Evidence : Type*} [DecidableEq Action]
    {policy : DesignStagedPolicy Action Evidence}
    {problem : DesignDecisionProblem Action Evidence} {evidence : Evidence}
    {actionStar : Action} {delta : ℝ}
    (hMem : actionStar ∈ problem.actions)
    (hRefute : designRefutationSound policy problem evidence)
    (hConfirm : designConfirmationSound policy problem evidence delta)
    (hConfirmCost : 0 < policy.confirmCost)
    (hRefuteCost : 0 ≤ policy.refuteCost)
    (hStrict : (designSurvivors policy problem.actions evidence).card < problem.actions.card) :
    actionStar ∈ designSurvivors policy problem.actions evidence ∧
      (∀ action ∈ designCertified policy problem.actions evidence,
        designDecisionCertificate problem evidence action
          (fun candidate => candidate ∈ designCertified policy problem.actions evidence) delta) ∧
      designStagedBudget policy problem.actions evidence <
        (problem.actions.card : ℝ) * policy.confirmCost +
          (problem.actions.card : ℝ) * policy.refuteCost := by
  refine ⟨designDecisionFocusedGuarantee hMem hRefute, ?_, ?_⟩
  · intro action hAction
    exact designStagedPolicyInstantiatesCertificate hConfirm hAction
  · exact designStagedBudgetSaving policy problem.actions evidence hConfirmCost hRefuteCost hStrict

end SafeSlice
