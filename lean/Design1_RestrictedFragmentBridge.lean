import Mathlib

noncomputable section

namespace SafeSlice

/-!
# Design 1: Restricted Fragment Bridge
-/

structure RestrictedFragmentBridge (Task Payload : Type*) where
  support : Set Task
  payload : Task → Option Payload

def obstructionFreeFragment {Task : Type*} (_tasks : Set Task) : Prop :=
  True

def designFragmentAdmissible {Task Payload : Type*}
    (bridge : RestrictedFragmentBridge Task Payload) (tasks : Set Task) : Prop :=
  tasks ⊆ bridge.support

theorem support_designFragmentAdmissible {Task Payload : Type*}
    (bridge : RestrictedFragmentBridge Task Payload) :
    designFragmentAdmissible bridge bridge.support := by
  intro task hTask
  exact hTask

def exportedTasks {Task Payload : Type*}
    (bridge : RestrictedFragmentBridge Task Payload) : Set Task :=
  {task | task ∈ bridge.support ∧ (bridge.payload task).isSome}

theorem exportedTasks_sub_support {Task Payload : Type*}
    (bridge : RestrictedFragmentBridge Task Payload) :
    exportedTasks bridge ⊆ bridge.support := by
  intro task hTask
  exact hTask.1

end SafeSlice
