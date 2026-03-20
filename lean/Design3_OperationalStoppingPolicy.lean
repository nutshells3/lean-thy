import Design2_JudgeStackInstantiation

noncomputable section

namespace SafeSlice

/-!
# Design 3: Operational Stopping Policy
-/

structure DesignConfidenceSequence where
  lower : Nat → ℝ
  upper : Nat → ℝ

inductive DesignStoppingDecision where
  | continueSampling
  | stopBelowThreshold
  | stopAboveThreshold
  deriving DecidableEq, Repr

def designCsCoversAt (cs : DesignConfidenceSequence) (trueError : ℝ) (t : Nat) : Prop :=
  cs.lower t ≤ trueError ∧ trueError ≤ cs.upper t

def designStoppingPolicy
    (cs : DesignConfidenceSequence) (etaMin etaMax : ℝ) (t : Nat) :
    DesignStoppingDecision :=
  if cs.upper t < etaMax then
    .stopBelowThreshold
  else if etaMin < cs.lower t then
    .stopAboveThreshold
  else
    .continueSampling

theorem designStoppingPolicyBelowSound
    {cs : DesignConfidenceSequence} {trueError etaMin etaMax : ℝ} {t : Nat}
    (hCover : designCsCoversAt cs trueError t)
    (hDecision : designStoppingPolicy cs etaMin etaMax t = .stopBelowThreshold) :
    trueError < etaMax := by
  have hUpper : trueError ≤ cs.upper t := hCover.2
  unfold designStoppingPolicy at hDecision
  by_cases hBelow : cs.upper t < etaMax
  · simp [hBelow] at hDecision
    linarith
  · by_cases hAbove : etaMin < cs.lower t
    · simp [hBelow, hAbove] at hDecision
    · simp [hBelow, hAbove] at hDecision

theorem designStoppingPolicyAboveSound
    {cs : DesignConfidenceSequence} {trueError etaMin etaMax : ℝ} {t : Nat}
    (hCover : designCsCoversAt cs trueError t)
    (hDecision : designStoppingPolicy cs etaMin etaMax t = .stopAboveThreshold) :
    etaMin < trueError := by
  have hLower : cs.lower t ≤ trueError := hCover.1
  unfold designStoppingPolicy at hDecision
  by_cases hBelow : cs.upper t < etaMax
  · simp [hBelow] at hDecision
  · by_cases hAbove : etaMin < cs.lower t
    · simp [hBelow, hAbove] at hDecision
      linarith
    · simp [hBelow, hAbove] at hDecision

structure OperationalStoppingPolicy (Task Payload : Type*) where
  instantiation : JudgeStackInstantiation Task Payload
  cs : DesignConfidenceSequence
  trueError : ℝ
  etaMin : ℝ
  etaMax : ℝ
  validAt : ∀ t, designCsCoversAt cs trueError t

theorem operationalPolicyCertifiesBelow {Task Payload : Type*}
    (policy : OperationalStoppingPolicy Task Payload) {t : Nat}
    (hDecision :
      designStoppingPolicy policy.cs policy.etaMin policy.etaMax t = .stopBelowThreshold) :
    policy.trueError < policy.etaMax :=
  designStoppingPolicyBelowSound (policy.validAt t) hDecision

end SafeSlice
