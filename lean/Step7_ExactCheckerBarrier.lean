import Mathlib

noncomputable section

namespace SafeSlice

/-!
# Step 7: Exact Checker Barrier

This is the mathematical side of the split. It exposes only the exact-checker
carrier and monotone lower-bound interface that the later theorem schemas use.
-/

structure ExactCheckerBarrier (Task : Type*) where
  successProb : Task → ℝ
  checkerAccepts : Task → Prop
  successNonneg : ∀ task, 0 ≤ successProb task
  successLeOne : ∀ task, successProb task ≤ 1

def verifiedSuccessAtLeast {Task : Type*}
    (barrier : ExactCheckerBarrier Task) (p : ℝ) (task : Task) : Prop :=
  p ≤ barrier.successProb task

def verifiedSuccessOn {Task : Type*}
    (barrier : ExactCheckerBarrier Task) (p : ℝ) (tasks : Set Task) : Prop :=
  ∀ ⦃task⦄, task ∈ tasks → verifiedSuccessAtLeast barrier p task

theorem verifiedSuccessOn_mono {Task : Type*}
    {barrier : ExactCheckerBarrier Task} {p : ℝ} {small large : Set Task}
    (hLarge : verifiedSuccessOn barrier p large) (hSubset : small ⊆ large) :
    verifiedSuccessOn barrier p small := by
  intro task hTask
  exact hLarge (hSubset hTask)

theorem verifiedSuccessAtLeast_nonneg {Task : Type*}
    (barrier : ExactCheckerBarrier Task) (task : Task) :
    verifiedSuccessAtLeast barrier 0 task :=
  barrier.successNonneg task

end SafeSlice
