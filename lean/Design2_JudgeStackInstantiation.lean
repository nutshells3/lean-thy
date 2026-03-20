import Design1_RestrictedFragmentBridge

noncomputable section

namespace SafeSlice

/-!
# Design 2: Judge-Stack Instantiation
-/

structure JudgeStackInstantiation (Task Payload : Type*) where
  bridge : RestrictedFragmentBridge Task Payload
  fastAbstainProb : Task → ℝ
  effectiveAcceptProb : Task → ℝ
  auditRadius : ℝ
  operationalLowerBound : Task → ℝ
  fastAbstain_nonneg : ∀ task, 0 ≤ fastAbstainProb task
  fastAbstain_le_one : ∀ task, fastAbstainProb task ≤ 1
  effectiveAccept_nonneg : ∀ task, 0 ≤ effectiveAcceptProb task
  effectiveAccept_le_one : ∀ task, effectiveAcceptProb task ≤ 1
  auditRadius_nonneg : 0 ≤ auditRadius
  lowerBound_sound : ∀ task, operationalLowerBound task ≤ effectiveAcceptProb task

def designTasks {Task Payload : Type*}
    (inst : JudgeStackInstantiation Task Payload) : Set Task :=
  inst.bridge.support

theorem operationalAuditLowerBound {Task Payload : Type*}
    (inst : JudgeStackInstantiation Task Payload) (task : Task) :
    inst.operationalLowerBound task ≤ inst.effectiveAcceptProb task :=
  inst.lowerBound_sound task

end SafeSlice
