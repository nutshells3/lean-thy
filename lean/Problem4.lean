import Mathlib

noncomputable section

namespace SafeSlice

/-!
# Problem 4 — Certified Deployment Frontier

Roadmap node 4A: characterize the feasible deployment frontier over four
node kinds (proof-carrying, statistical, cheap-judge, human) under explicit
risk and cost budgets.

The proof-carrying node embeds a semantically closed 7A-lite witness
(Problem 3's `GlobalForm` with `FragmentAdmissible` proof).  The other
three node kinds are abstract: their risk and cost are parameters of
the `DeployConfig` carrier.
-/

/-! ## Node kinds -/

/-- The four node types that can appear in a certified deployment. -/
inductive NodeKind where
  | proofCarrying
  | statistical
  | cheapJudge
  | human
deriving DecidableEq, Fintype, Repr

open NodeKind

/-! ## Deployment configuration -/

/-- A deployment configuration assigns a finite set of obligations to each
node kind together with measurable risk and cost values per kind.

Risk and cost are valued in `NNReal` (non-negative reals). -/
structure DeployConfig (Ob : Type _) where
  /-- Which obligations are handled by each node kind. -/
  assignment : NodeKind → Finset Ob
  /-- Risk contributed by each node kind. -/
  risk : NodeKind → NNReal
  /-- Cost contributed by each node kind. -/
  cost : NodeKind → NNReal

section Deploy

variable {Ob : Type _} [DecidableEq Ob]

/-! ## Risk and Cost aggregation -/

/-- Total risk of a deployment configuration (sum over node kinds). -/
def DeployConfig.totalRisk (cfg : DeployConfig Ob) : NNReal :=
  Finset.univ.sum cfg.risk

/-- Total cost of a deployment configuration (sum over node kinds). -/
def DeployConfig.totalCost (cfg : DeployConfig Ob) : NNReal :=
  Finset.univ.sum cfg.cost

/-! ## Feasibility predicate -/

/-- A deployment is feasible when total risk ≤ riskBound and
total cost ≤ costBound. -/
def Feasible (riskBound costBound : NNReal) (cfg : DeployConfig Ob) : Prop :=
  cfg.totalRisk ≤ riskBound ∧ cfg.totalCost ≤ costBound

/-- A deployment covers a goal obligation set when every goal is assigned
to at least one node kind. -/
def Covers (goals : Finset Ob) (cfg : DeployConfig Ob) : Prop :=
  goals ⊆ Finset.univ.biUnion cfg.assignment

/-! ## Proof-carrying node discipline

The proof-carrying node is the strongest: it contributes zero risk.
This is the interface contract that ties the deployment frontier back to
the 7A-lite constructive witness from Problem 3. -/

/-- A deployment configuration satisfies proof-carrying discipline when
the proof-carrying node's risk is zero. -/
def ProofCarryingDiscipline (cfg : DeployConfig Ob) : Prop :=
  cfg.risk proofCarrying = 0

/-! ## Deployment frontier (Pareto minimality) -/

/-- A feasible configuration `cfg` is on the deployment frontier relative
to a set of configurations `S` when no other feasible configuration in `S`
strictly dominates it on both risk and cost while covering the same goals. -/
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

/-! ## Frontier existence (statement)

Given any nonempty finite set of feasible covering configurations, a
Pareto-minimal element exists on the risk dimension. -/

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

/-! ## Proof-carrying discipline lowers frontier risk

When the proof-carrying node has zero risk, total risk equals the sum
over the three non-proof kinds. -/

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
