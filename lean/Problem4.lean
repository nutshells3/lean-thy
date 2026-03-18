import Mathlib

noncomputable section

namespace SafeSlice

inductive NodeKind where
  | proofCarrying
  | statistical
  | cheapJudge
  | human
deriving DecidableEq, Fintype, Repr

open NodeKind

structure DeployConfig (Ob : Type _) where

  assignment : NodeKind → Finset Ob

  risk : NodeKind → NNReal

  cost : NodeKind → NNReal

section Deploy

variable {Ob : Type _} [DecidableEq Ob]

def DeployConfig.totalRisk (cfg : DeployConfig Ob) : NNReal :=
  Finset.univ.sum cfg.risk

def DeployConfig.totalCost (cfg : DeployConfig Ob) : NNReal :=
  Finset.univ.sum cfg.cost

def Feasible (riskBound costBound : NNReal) (cfg : DeployConfig Ob) : Prop :=
  cfg.totalRisk ≤ riskBound ∧ cfg.totalCost ≤ costBound

def Covers (goals : Finset Ob) (cfg : DeployConfig Ob) : Prop :=
  goals ⊆ Finset.univ.biUnion cfg.assignment

def ProofCarryingDiscipline (cfg : DeployConfig Ob) : Prop :=
  cfg.risk proofCarrying = 0

def OnFrontier
    (goals : Finset Ob) (riskBound costBound : NNReal)
    (S : Set (DeployConfig Ob))
    (cfg : DeployConfig Ob) : Prop :=
  cfg ∈ S ∧
  Covers goals cfg ∧
  Feasible riskBound costBound cfg ∧
  ¬ ∃ cfg' ∈ S,
      Covers goals cfg' ∧
      Feasible riskBound costBound cfg' ∧
      (cfg'.totalRisk ≤ cfg.totalRisk ∧ cfg'.totalCost ≤ cfg.totalCost) ∧
      (cfg'.totalRisk < cfg.totalRisk ∨ cfg'.totalCost < cfg.totalCost)

theorem frontier_exists
    {goals : Finset Ob} {riskBound costBound : NNReal}
    {S : Finset (DeployConfig Ob)}
    (hne : S.Nonempty)
    (hfeas : ∀ cfg ∈ S, Covers goals cfg ∧ Feasible riskBound costBound cfg) :
    ∃ cfg ∈ S, OnFrontier goals riskBound costBound (↑S) cfg := by
  obtain ⟨cfg, hcfg, hmin⟩ :=
    Finset.exists_min_image S (fun c => c.totalRisk + c.totalCost) hne
  refine ⟨cfg, hcfg, Finset.mem_coe.mpr hcfg, (hfeas cfg hcfg).1, (hfeas cfg hcfg).2, ?_⟩
  rintro ⟨cfg', hcfg'S, -, -, ⟨hr, hc⟩, hstrict⟩
  have hcfg'mem : cfg' ∈ S := Finset.mem_coe.mp hcfg'S
  have hsub := hmin cfg' hcfg'mem
  rcases hstrict with h | h
  · exact absurd (add_lt_add_of_lt_of_le h hc) (not_lt.mpr hsub)
  · exact absurd (add_lt_add_of_le_of_lt hr h) (not_lt.mpr hsub)

omit [DecidableEq Ob] in
theorem proofCarrying_lowers_risk
    (cfg : DeployConfig Ob)
    (hpc : ProofCarryingDiscipline cfg) :
    cfg.totalRisk =
      cfg.risk statistical + cfg.risk cheapJudge + cfg.risk human := by
  simp only [DeployConfig.totalRisk, ProofCarryingDiscipline] at *
  have huniv : Finset.univ = ({proofCarrying, statistical, cheapJudge, human} : Finset NodeKind) :=
    by decide
  rw [huniv]
  simp [hpc]
  ring

end Deploy

end SafeSlice
