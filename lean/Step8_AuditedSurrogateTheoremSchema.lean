import Step7_ExactCheckerBarrier

noncomputable section

namespace SafeSlice

/-!
# Step 8: Audited Surrogate Theorem Schema

This file stays on the mathematical branch. It packages the fast/gold
acceptance probabilities and the degraded lower bound as abstract theorem
schema data.
-/

structure AuditedSurrogateTheoremSchema (Task : Type*) where
  barrier : ExactCheckerBarrier Task
  fastAccept : Task → ℝ
  goldAccept : Task → ℝ
  disagreement : Task → ℝ
  fastAccept_nonneg : ∀ task, 0 ≤ fastAccept task
  fastAccept_le_one : ∀ task, fastAccept task ≤ 1
  goldAccept_nonneg : ∀ task, 0 ≤ goldAccept task
  goldAccept_le_one : ∀ task, goldAccept task ≤ 1
  disagreement_nonneg : ∀ task, 0 ≤ disagreement task
  disagreement_le_one : ∀ task, disagreement task ≤ 1
  degraded_lower_bound : ∀ task, fastAccept task - disagreement task ≤ goldAccept task

def auditErrorAtMost {Task : Type*}
    (schema : AuditedSurrogateTheoremSchema Task) (task : Task) (η : ℝ) : Prop :=
  schema.disagreement task ≤ η

theorem degradedFastToGoldLowerBound {Task : Type*}
    (schema : AuditedSurrogateTheoremSchema Task) (task : Task) :
    schema.fastAccept task - schema.disagreement task ≤ schema.goldAccept task :=
  schema.degraded_lower_bound task

theorem degradedWithAuditBound {Task : Type*}
    (schema : AuditedSurrogateTheoremSchema Task) (task : Task) {η : ℝ}
    (hAudit : auditErrorAtMost schema task η) :
    schema.fastAccept task - η ≤ schema.goldAccept task := by
  have hBase := schema.degraded_lower_bound task
  dsimp [auditErrorAtMost] at hAudit
  linarith

def taskAuditErrorAtMost {Task : Type*}
    (schema : AuditedSurrogateTheoremSchema Task) (η : ℝ) (tasks : Set Task) : Prop :=
  ∀ ⦃task⦄, task ∈ tasks → auditErrorAtMost schema task η

theorem taskAuditBoundImpGoldLower {Task : Type*}
    (schema : AuditedSurrogateTheoremSchema Task) {η : ℝ} {tasks : Set Task}
    (hAudit : taskAuditErrorAtMost schema η tasks) {task : Task} (hTask : task ∈ tasks) :
    schema.fastAccept task - η ≤ schema.goldAccept task :=
  degradedWithAuditBound schema task (hAudit hTask)

end SafeSlice
