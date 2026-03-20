import Step10_VarianceAdaptiveBoundTheorem

noncomputable section

namespace SafeSlice

/-!
# Step 11: Decision-Focused Certification Theorem
-/

inductive Decision where
  | accept
  | reject
  | defer
  deriving DecidableEq, Repr

structure DecisionProblem (Action Evidence : Type*) [DecidableEq Action] where
  actions : Finset Action
  utility : Action → Evidence → ℝ
  cost : Action → Evidence → ℝ

def optimalAction {Action Evidence : Type*} [DecidableEq Action]
    (problem : DecisionProblem Action Evidence) (evidence : Evidence) (action : Action) : Prop :=
  action ∈ problem.actions ∧
    ∀ action' ∈ problem.actions,
      problem.utility action evidence - problem.cost action evidence ≥
        problem.utility action' evidence - problem.cost action' evidence

def decisionGap {Action Evidence : Type*} [DecidableEq Action]
    (problem : DecisionProblem Action Evidence) (evidence : Evidence)
    (action action' : Action) : ℝ :=
  (problem.utility action evidence - problem.cost action evidence) -
    (problem.utility action' evidence - problem.cost action' evidence)

theorem optimalAction_gap {Action Evidence : Type*} [DecidableEq Action]
    {problem : DecisionProblem Action Evidence} {evidence : Evidence}
    {action action' : Action}
    (hOptimal : optimalAction problem evidence action)
    (hMem : action' ∈ problem.actions) :
    0 ≤ decisionGap problem evidence action action' := by
  rcases hOptimal with ⟨_, hOptimality⟩
  have hCompare := hOptimality action' hMem
  dsimp [decisionGap]
  linarith

def decisionCertificate {Action Evidence : Type*} [DecidableEq Action]
    (problem : DecisionProblem Action Evidence) (evidence : Evidence)
    (action : Action) (certify : Action → Prop) (δ : ℝ) : Prop :=
  action ∈ problem.actions ∧
    certify action ∧
    ∀ action' ∈ problem.actions, -δ ≤ decisionGap problem evidence action action'

theorem decisionCertificateNearOptimal {Action Evidence : Type*} [DecidableEq Action]
    {problem : DecisionProblem Action Evidence} {evidence : Evidence}
    {action action' : Action} {certify : Action → Prop} {δ : ℝ}
    (hCert : decisionCertificate problem evidence action certify δ)
    (hMem : action' ∈ problem.actions) :
    -δ ≤ decisionGap problem evidence action action' :=
  hCert.2.2 action' hMem

end SafeSlice
