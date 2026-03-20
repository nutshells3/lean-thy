import Mathlib
import Problem3
import Problem5

noncomputable section

namespace SafeSlice

/-!
# Problem 6

This file formalizes Deploy(G, M) as proposer reach intersected with an
admissibility regime, and relates that decomposition to the frontier and
bank constructions from Problems 3 and 5.
-/

/-! ## Core types -/

/-- A **proposer** (generator) G that can reach a set of semantic objects.
    Parametric over `Sem`, the type of semantic objects. -/
structure Proposer (Sem : Type*) where
  /-- The set of semantic objects reachable by this proposer. -/
  reach : Set Sem

/-- An **admissibility regime** M = (C, R, V, P) governing which semantics
    are deployable. The four components are:
    - `constraints` : structural well-formedness conditions
    - `riskBound`   : maximum tolerable risk
    - `riskMeasure`  : assigns a risk level to each semantic object
    - `validator`   : semantic acceptance predicate
    - `policy`      : deployment policy predicate -/
structure AdmRegime (Sem : Type*) where
  constraints : Sem → Prop
  riskBound   : NNReal
  riskMeasure : Sem → NNReal
  validator   : Sem → Prop
  policy      : Sem → Prop

/-! ## Derived sets -/

/-- The reachable envelope of a proposer. -/
def Reach {Sem : Type*} (G : Proposer Sem) : Set Sem := G.reach

/-- The admissible envelope of a regime: the set of semantics satisfying all
    four regime components simultaneously, including the risk bound. -/
def Adm {Sem : Type*} (M : AdmRegime Sem) : Set Sem :=
  { s | M.constraints s ∧ M.riskMeasure s ≤ M.riskBound ∧ M.validator s ∧ M.policy s }

/-- **Deployable semantics**: the intersection of what the proposer can reach
    and what the regime admits. -/
def Deploy {Sem : Type*} (G : Proposer Sem) (M : AdmRegime Sem) : Set Sem :=
  Reach G ∩ Adm M

/-- Deploy unfolds to the expected intersection. -/
theorem deploy_eq_inter {Sem : Type*} (G : Proposer Sem) (M : AdmRegime Sem) :
    Deploy G M = Reach G ∩ Adm M := rfl

/-! ## 4A connector: constructive scope = reachable envelope

In Problem 3, `CertifiedFrontier` establishes `scope.constructive ⊆ chainExports chain`.
Here we model the chain-based proposer whose reach is exactly `chainExports`, and
show that the constructive scope equals the reachable envelope when the scope is
tight (equality rather than just subset). -/

/-- Abstract model of the 4A surface: a constructive scope backed by chain
    exports from a fragment-admissible composable chain. -/
structure ConstructiveConnector (Claim : Type*) where
  /-- The constructive scope (Problem 3's `TaskScope.constructive`). -/
  constructiveScope : Finset Claim
  /-- The chain exports (Problem 3's `chainExports chain`). -/
  chainExports : Finset Claim
  /-- The certified frontier guarantee: constructive scope ⊆ chain exports. -/
  scope_sub_exports : constructiveScope ⊆ chainExports

/-- The chain-based proposer: reach is exactly the chain exports. -/
def chainProposer {Claim : Type*} (conn : ConstructiveConnector Claim) :
    Proposer Claim where
  reach := { c | c ∈ conn.chainExports }

/-- **4A tight connector**: when the constructive scope equals chain exports,
    the reachable envelope of the chain-based proposer is exactly the
    constructive scope. -/
theorem connector_4A_tight {Claim : Type*}
    (conn : ConstructiveConnector Claim)
    (htight : conn.constructiveScope = conn.chainExports) :
    Reach (chainProposer conn) = { c | c ∈ conn.constructiveScope } := by
  simp only [Reach, chainProposer, htight]

/-- **4A gap characterization**: when equality fails, the deployment gap is
    exactly `chainExports \ constructiveScope`. -/
theorem connector_4A_gap {Claim : Type*} [DecidableEq Claim]
    (conn : ConstructiveConnector Claim) :
    { c | c ∈ conn.chainExports } \ { c | c ∈ conn.constructiveScope } =
    { c | c ∈ conn.chainExports \ conn.constructiveScope } := by
  ext c; simp [Finset.mem_sdiff]

/-! ## 4B connector: bank semantics = Deploy(G, M)

In Problem 5, `CertifiedBank` retains proposals passing a validator.
Here we define bank semantics as the set of semantics realized by bank members,
then prove it equals `Deploy(G, M)` under explicit coverage. -/

/-- A `realizes` relation connecting bank proposals to semantic objects. -/
structure BankBridge (PId Compiled Sem : Type*) where
  /-- Which semantic object a compiled proposal realizes. -/
  realize : PId → Compiled → Sem

/-- The **bank semantics**: the set of semantic objects realized by some
    member of a certified bank (using Problem 5's `CertifiedBank` shape). -/
def bankSemantics {PId Compiled Sem : Type*}
    (members : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Sem) : Set Sem :=
  { s | ∃ pid comp, (pid, comp) ∈ members ∧ bridge.realize pid comp = s }

/-- **Coverage assumption**: every deployable semantic has a realizing proposal
    in the bank. This is the explicit load-bearing assumption. -/
def BankCoversDeployable {PId Compiled Sem : Type*}
    (members : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Sem)
    (deployable : Set Sem) : Prop :=
  ∀ s ∈ deployable, ∃ pid comp, (pid, comp) ∈ members ∧ bridge.realize pid comp = s

/-- A **sound bank**: a bank whose members all realize deployable semantics.
    Soundness is structural (baked into the bank construction), not an
    external assumption. -/
structure SoundBank (PId Compiled Sem : Type*) (deployable : Set Sem) where
  members : Set (PId × Compiled)
  bridge  : BankBridge PId Compiled Sem
  sound   : ∀ pid comp, (pid, comp) ∈ members → bridge.realize pid comp ∈ deployable

/-- **4B connector theorem**: under the explicit coverage assumption alone
    (soundness is structural in `SoundBank`), bank semantics equals
    `Deploy(G, M)`. -/
theorem connector_4B_bank_eq_deploy {PId Compiled Sem : Type*}
    (G : Proposer Sem)
    (M : AdmRegime Sem)
    (bank : SoundBank PId Compiled Sem (Deploy G M))
    (hcov : BankCoversDeployable bank.members bank.bridge (Deploy G M)) :
    bankSemantics bank.members bank.bridge = Deploy G M := by
  ext s
  constructor
  · rintro ⟨pid, comp, hmem, rfl⟩
    exact bank.sound pid comp hmem
  · intro hs
    exact hcov s hs

/-! ## Exact admissible-envelope characterization

The admissible envelope `Adm M` decomposes into the conjunction of its
four regime components. This section characterizes the envelope exactly
and states monotonicity properties. -/

/-- `Adm M` is the intersection of constraint, risk-bound, validator, and policy sets. -/
theorem adm_eq_inter {Sem : Type*} (M : AdmRegime Sem) :
    Adm M = { s | M.constraints s } ∩ { s | M.riskMeasure s ≤ M.riskBound } ∩
            { s | M.validator s } ∩ { s | M.policy s } := by
  ext s
  simp only [Adm, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

/-- Weakening any regime component enlarges the admissible envelope. -/
theorem adm_monotone_weaken {Sem : Type*}
    (M₁ M₂ : AdmRegime Sem)
    (hc : ∀ s, M₁.constraints s → M₂.constraints s)
    (hr : ∀ s, M₁.riskMeasure s ≤ M₁.riskBound → M₂.riskMeasure s ≤ M₂.riskBound)
    (hv : M₁.validator = M₂.validator)
    (hp : M₁.policy = M₂.policy) :
    Adm M₁ ⊆ Adm M₂ := by
  intro s ⟨hcs, hrs, hvs, hps⟩
  exact ⟨hc s hcs, hr s hrs, hv ▸ hvs, hp ▸ hps⟩

/-! ## Generator-invariance under fixed admissibility

Two proposers with the same reachable envelope produce the same deployable
set under any fixed regime. -/

/-- **Generator-invariance**: `Deploy` depends only on `Reach G`, not on the
    internal structure of the proposer. -/
theorem deploy_generator_invariant {Sem : Type*}
    (G₁ G₂ : Proposer Sem) (M : AdmRegime Sem)
    (hreach : Reach G₁ = Reach G₂) :
    Deploy G₁ M = Deploy G₂ M := by
  simp only [Deploy, hreach]

/-! ## Conservative-upgrade theorem

Expanding the proposer's reach while keeping the regime fixed can only enlarge
(never shrink) the deployable set. -/

/-- **Conservative-upgrade**: if `G₂` reaches everything `G₁` does, then
    `Deploy(G₁, M) ⊆ Deploy(G₂, M)`. -/
theorem deploy_conservative_upgrade {Sem : Type*}
    (G₁ G₂ : Proposer Sem) (M : AdmRegime Sem)
    (hexp : Reach G₁ ⊆ Reach G₂) :
    Deploy G₁ M ⊆ Deploy G₂ M :=
  Set.inter_subset_inter_left _ hexp

/-! ## Proposal-axis reachable-envelope theorem

The reachable envelope of the union of two proposers is the union of their
individual envelopes. -/

/-- Combined proposer whose reach is the union. -/
def Proposer.combine {Sem : Type*} (G₁ G₂ : Proposer Sem) : Proposer Sem where
  reach := G₁.reach ∪ G₂.reach

/-- **Reachable-envelope union**: `Reach(G₁ ∪ G₂) = Reach G₁ ∪ Reach G₂`. -/
theorem reach_combine {Sem : Type*} (G₁ G₂ : Proposer Sem) :
    Reach (G₁.combine G₂) = Reach G₁ ∪ Reach G₂ := rfl

/-- **Deploy distributes over proposer combination**. -/
theorem deploy_combine {Sem : Type*}
    (G₁ G₂ : Proposer Sem) (M : AdmRegime Sem) :
    Deploy (G₁.combine G₂) M = Deploy G₁ M ∪ Deploy G₂ M := by
  simp only [Deploy, reach_combine, Set.union_inter_distrib_right]

/-! ## External-novelty barrier

An external proposer can contribute new deployable semantics only if its reach
extends beyond the current proposer's reach into the admissible region. -/

/-- **Novelty barrier**: any semantic in `Deploy(G_ext, M) \ Deploy(G, M)`
    must lie in `Reach(G_ext) \ Reach(G)`. -/
theorem external_novelty_barrier {Sem : Type*}
    (G G_ext : Proposer Sem) (M : AdmRegime Sem) :
    Deploy G_ext M \ Deploy G M ⊆
    (Reach G_ext \ Reach G) ∩ Adm M := by
  intro s ⟨⟨hr_ext, ha⟩, hndep⟩
  exact ⟨⟨hr_ext, fun hr => hndep ⟨hr, ha⟩⟩, ha⟩

/-! ## Transfer-dominance corollary under fixed regimes

When one proposer's reach dominates another's under a fixed regime,
deployable semantics are monotone. This is the economic corollary:
expanding generation capacity under fixed compliance never loses
previously deployable semantics. -/

/-- **Transfer-dominance**: under fixed `M`, if `Reach G₁ ⊆ Reach G₂`,
    then every `s ∈ Deploy(G₁, M)` is also in `Deploy(G₂, M)`. -/
theorem transfer_dominance {Sem : Type*}
    (G₁ G₂ : Proposer Sem) (M : AdmRegime Sem)
    (hdom : Reach G₁ ⊆ Reach G₂) :
    Deploy G₁ M ⊆ Deploy G₂ M :=
  deploy_conservative_upgrade G₁ G₂ M hdom

/-- **Regime-saturation**: when `Reach G` already contains all of `Adm M`,
    the deployable set equals the admissible envelope exactly. -/
theorem regime_saturation {Sem : Type*}
    (G : Proposer Sem) (M : AdmRegime Sem)
    (hsat : Adm M ⊆ Reach G) :
    Deploy G M = Adm M := by
  ext s
  constructor
  · exact fun ⟨_, ha⟩ => ha
  · exact fun ha => ⟨hsat ha, ha⟩

/-! ## Coverage-gap characterization (Q_A.1)

When coverage fails, the gap is exactly the set of deployable semantics
with no realizing bank member. -/

/-- The **coverage gap**: deployable semantics not realized by any bank member. -/
def coverageGap {PId Compiled Sem : Type*}
    (members : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Sem)
    (deployable : Set Sem) : Set Sem :=
  deployable \ bankSemantics members bridge

/-- The coverage gap is empty iff the bank covers all deployable semantics. -/
theorem coverageGap_empty_iff {PId Compiled Sem : Type*}
    (members : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Sem)
    (deployable : Set Sem) :
    coverageGap members bridge deployable = ∅ ↔
    BankCoversDeployable members bridge deployable := by
  simp only [coverageGap, BankCoversDeployable, bankSemantics,
    Set.diff_eq_empty, Set.subset_def, Set.mem_setOf_eq]

/-- Under a sound bank, the gap is a subset of the deployable set. -/
theorem coverageGap_sub_deployable {PId Compiled Sem : Type*}
    (members : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Sem)
    (deployable : Set Sem) :
    coverageGap members bridge deployable ⊆ deployable :=
  Set.diff_subset

/-! ## Surjective-proposer elimination (Q_E.1)

When the proposer is surjective (its reach is the universal set),
the reachable envelope can be eliminated: `Deploy(G, M) = Adm M`. -/

/-- **Surjective-proposer elimination**: if `Reach G = Set.univ`, then
    `Deploy(G, M) = Adm M`. This answers Q_E.1 affirmatively. -/
theorem deploy_surjective_proposer {Sem : Type*}
    (G : Proposer Sem) (M : AdmRegime Sem)
    (hsurj : Reach G = Set.univ) :
    Deploy G M = Adm M := by
  simp only [Deploy, hsurj, Set.univ_inter]

/-! ## Weakest-coverage equality (Q_E.3)

The weakest condition under which bank semantics equals the deployable set
is exactly full coverage (no gap). This follows from the 4B connector. -/

/-- **Weakest-coverage sufficiency**: soundness plus full coverage is both
    necessary and sufficient for `bankSemantics = Deploy(G, M)`. -/
theorem bank_eq_deploy_iff {PId Compiled Sem : Type*}
    (G : Proposer Sem) (M : AdmRegime Sem)
    (bank : SoundBank PId Compiled Sem (Deploy G M)) :
    bankSemantics bank.members bank.bridge = Deploy G M ↔
    BankCoversDeployable bank.members bank.bridge (Deploy G M) := by
  constructor
  · intro heq s hs
    rw [← heq] at hs
    exact hs
  · exact connector_4B_bank_eq_deploy G M bank

/-! ## Regime-weakening and Deploy monotonicity (Q_A.3)

Deploy is monotone in the admissibility regime: weakening the regime
can only enlarge the deployable set. -/

/-- **Deploy monotone in regime**: if `Adm M₁ ⊆ Adm M₂`, then
    `Deploy(G, M₁) ⊆ Deploy(G, M₂)`. -/
theorem deploy_monotone_regime {Sem : Type*}
    (G : Proposer Sem) (M₁ M₂ : AdmRegime Sem)
    (hadm : Adm M₁ ⊆ Adm M₂) :
    Deploy G M₁ ⊆ Deploy G M₂ :=
  Set.inter_subset_inter_right _ hadm

/-! ## Config-independence of bankSemantics (Q_Ab.1)

`bankSemantics` depends only on the `members` set and `bridge` relation,
not on any ambient configuration. This is structural: the definition is
parametric. The following witnesses that two banks with the same members
and bridge produce the same semantics. -/

/-- **Config-independence**: bank semantics is determined entirely by
    `members` and `bridge`. -/
theorem bankSemantics_config_independent {PId Compiled Sem : Type*}
    (members : Set (PId × Compiled))
    (b₁ b₂ : BankBridge PId Compiled Sem)
    (hbridge : b₁.realize = b₂.realize) :
    bankSemantics members b₁ = bankSemantics members b₂ := by
  simp only [bankSemantics, hbridge]

/-! ## Live 4A connector: over Problem 3's CertifiedFrontier / chainExports

Problem 3's `CertifiedFrontier df` guarantees `df.scope.constructive ⊆ chainExports df.chain`.
The following theorems state the 4A connector directly over those Finsets,
so the bridge works with Problem 3's actual objects by extraction. -/

/-- Build a proposer whose reach is exactly a Finset (e.g. `chainExports chain`). -/
def finsetProposer {Claim : Type*} (exports : Finset Claim) : Proposer Claim where
  reach := { c | c ∈ exports }

/-- The constructive scope of a certified frontier lies in the reach
    of the chain-exports proposer. -/
theorem live_connector_4A {Claim : Type*}
    (chainExp : Finset Claim)
    (constructiveScope : Finset Claim)
    (hcov : constructiveScope ⊆ chainExp) :
    { c | c ∈ constructiveScope } ⊆ Reach (finsetProposer chainExp) := by
  intro c hc
  simp only [Reach, finsetProposer, Set.mem_setOf_eq] at *
  exact hcov hc

/-- **Live 4A tight connector**: when the constructive scope equals
    chain exports, the reachable envelope equals the constructive scope
    exactly. -/
theorem live_connector_4A_tight {Claim : Type*}
    (chainExp : Finset Claim)
    (constructiveScope : Finset Claim)
    (htight : constructiveScope = chainExp) :
    Reach (finsetProposer chainExp) = { c | c ∈ constructiveScope } := by
  simp only [Reach, finsetProposer, htight]

/-- **Live 4A residual-gap theorem**: the gap between the proposer's reach and
    the constructive scope is exactly `chainExp \ constructiveScope`, giving
    an exact residual-gap characterization from Problem 3's objects. -/
theorem live_connector_4A_residual_gap {Claim : Type*} [DecidableEq Claim]
    (chainExp constructiveScope : Finset Claim) :
    Reach (finsetProposer chainExp) \ { c | c ∈ constructiveScope } =
    { c | c ∈ chainExp \ constructiveScope } := by
  ext c; simp [Reach, finsetProposer, Finset.mem_sdiff]

/-! ## Live 4B connector: over Problem 5's CertifiedBank / soundRetention

Problem 5's `soundRetention` guarantees every member of a `CertifiedBank` passes
the validator. The following constructs a Problem 6 `SoundBank` from
(PId × Compiled) member pairs with a soundness proof matching Problem 5's
shape, then shows bank semantics equals `Deploy(G, M)` under coverage. -/

/-- **Live 4B connector**: given member pairs with a soundness certificate
    matching Problem 5's `soundRetention` guarantee, bank semantics equals
    `Deploy(G, M)` under explicit coverage.
    Instantiate `memberPairs` and `hsound` from Problem 5's `CertifiedBank`
    by extracting `(fp.proposalId, fp.form)` pairs. -/
theorem live_connector_4B {PId Compiled Sem : Type*}
    (G : Proposer Sem) (M : AdmRegime Sem)
    (memberPairs : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Sem)
    (hsound : ∀ pid comp, (pid, comp) ∈ memberPairs →
      bridge.realize pid comp ∈ Deploy G M)
    (hcov : BankCoversDeployable memberPairs bridge (Deploy G M)) :
    bankSemantics memberPairs bridge = Deploy G M :=
  connector_4B_bank_eq_deploy G M ⟨memberPairs, bridge, hsound⟩ hcov

/-! ## 7A-lite direct witness characterization

The 4A and 4B connectors compose into a direct characterization:
deployable semantics from a chain-exports proposer are exactly those
chain exports that are also admissible. -/

/-- **7A-lite witness characterization**: deployable semantics under a
    chain-exports proposer equal `{c | c ∈ chainExp} ∩ Adm M`. -/
theorem witness_7A_lite {Claim : Type*}
    (chainExp : Finset Claim)
    (M : AdmRegime Claim) :
    Deploy (finsetProposer chainExp) M =
    { c | c ∈ chainExp } ∩ Adm M := rfl

/-- **7A-lite bank composition**: the 4A and 4B connectors compose directly.
    Under soundness and coverage, bank semantics equals chain exports
    intersected with the admissible envelope — the direct witness
    characterization without going through intermediate `Deploy`. -/
theorem connector_4A_4B_compose {Claim PId Compiled : Type*}
    (chainExp : Finset Claim)
    (M : AdmRegime Claim)
    (memberPairs : Set (PId × Compiled))
    (bridge : BankBridge PId Compiled Claim)
    (hsound : ∀ pid comp, (pid, comp) ∈ memberPairs →
      bridge.realize pid comp ∈ Deploy (finsetProposer chainExp) M)
    (hcov : BankCoversDeployable memberPairs bridge
      (Deploy (finsetProposer chainExp) M)) :
    bankSemantics memberPairs bridge = { c | c ∈ chainExp } ∩ Adm M :=
  connector_4B_bank_eq_deploy _ M ⟨memberPairs, bridge, hsound⟩ hcov

/-! ## Closure-bounded recombination theorem

Combining two frontier proposers under a single regime produces exactly
the union of their individual deployable sets. This provides an explicit
recombination bound. -/

/-- **Closure-bounded recombination**: combining two chain-export proposers
    under one regime yields exactly the union of individual deployable sets. -/
theorem closure_bounded_recombination {Claim : Type*}
    (chainExp₁ chainExp₂ : Finset Claim)
    (M : AdmRegime Claim) :
    Deploy ((finsetProposer chainExp₁).combine (finsetProposer chainExp₂)) M =
    Deploy (finsetProposer chainExp₁) M ∪ Deploy (finsetProposer chainExp₂) M :=
  deploy_combine _ _ M

/-- **Recombination novelty bound**: when adding a second frontier, the
    new deployable content is bounded by the second frontier's chain exports
    minus the first, intersected with the admissible envelope. -/
theorem recombination_novelty_bound {Claim : Type*}
    (chainExp₁ chainExp₂ : Finset Claim)
    (M : AdmRegime Claim) :
    Deploy (finsetProposer chainExp₂) M \ Deploy (finsetProposer chainExp₁) M ⊆
    (Reach (finsetProposer chainExp₂) \ Reach (finsetProposer chainExp₁)) ∩ Adm M :=
  external_novelty_barrier _ _ M

/-! ## Direct 4A connector: over Problem 3's DeploymentFrontier + CertifiedFrontier

The following theorems accept Problem 3's actual `DeploymentFrontier` and
`CertifiedFrontier` proof directly, closing the gap between the extracted-shape
live connectors and the live Problem 3 objects. -/

/-- **Direct 4A connector**: the constructive scope of a certified deployment
    frontier is contained in the reachable envelope of the chain-exports proposer.
    Takes Problem 3's `DeploymentFrontier` and `CertifiedFrontier` directly. -/
theorem direct_connector_4A
    {SliceId Claim Question : Type*} [DecidableEq Claim]
    (df : DeploymentFrontier SliceId Claim Question)
    (hcert : CertifiedFrontier df) :
    { c | c ∈ df.scope.constructive } ⊆
    Reach (finsetProposer (chainExports df.chain)) :=
  live_connector_4A _ _ (certifiedFrontier_constructive_covered df hcert)

/-- **Direct 4A tight connector**: when scope equality holds, the reachable
    envelope equals the constructive scope exactly. -/
theorem direct_connector_4A_tight
    {SliceId Claim Question : Type*} [DecidableEq Claim]
    (df : DeploymentFrontier SliceId Claim Question)
    (_hcert : CertifiedFrontier df)
    (htight : df.scope.constructive = chainExports df.chain) :
    Reach (finsetProposer (chainExports df.chain)) =
    { c | c ∈ df.scope.constructive } :=
  live_connector_4A_tight _ _ htight

/-- **Direct 4A residual-gap theorem**: the exact gap between the chain-exports
    proposer's reach and the constructive scope, stated over Problem 3's
    `DeploymentFrontier`. -/
theorem direct_connector_4A_residual_gap
    {SliceId Claim Question : Type*} [DecidableEq Claim]
    (df : DeploymentFrontier SliceId Claim Question) :
    Reach (finsetProposer (chainExports df.chain)) \
      { c | c ∈ df.scope.constructive } =
    { c | c ∈ chainExports df.chain \ df.scope.constructive } :=
  live_connector_4A_residual_gap _ _

/-! ## Direct 4B connector: over Problem 5's CertifiedBank + soundRetention

The following theorems accept Problem 5's actual `CertifiedBank` type directly
and build the bridge to Problem 6's `Deploy(G, M)` equality. -/

/-- Extract `(PId × Compiled)` pairs from a Problem 5 `CertifiedBank`. -/
def CertifiedBank.toPairs {PId Compiled : Type*}
    (bank : CertifiedBank PId Compiled) : Set (PId × Compiled) :=
  { p | ∃ fp ∈ bank.members, p = (fp.proposalId, fp.form) }

/-- **Direct 4B connector**: given a Problem 5 `CertifiedBank` and a linking
    hypothesis that validator-passing proposals realize deployable semantics,
    bank semantics equals `Deploy(G, M)` under explicit coverage.
    Soundness is lifted through Problem 5's `soundRetention` guarantee
    rather than assumed as a fresh member-by-member hypothesis. -/
theorem direct_connector_4B
    {PId Compiled Sem : Type*}
    (G : Proposer Sem) (M : AdmRegime Sem)
    (bank : CertifiedBank PId Compiled)
    (bridge : BankBridge PId Compiled Sem)
    (hlink : ∀ fp : FormalizedProposal PId Compiled,
      fp.passes bank.validator →
      bridge.realize fp.proposalId fp.form ∈ Deploy G M)
    (hcov : BankCoversDeployable bank.toPairs bridge (Deploy G M)) :
    bankSemantics bank.toPairs bridge = Deploy G M := by
  apply live_connector_4B G M bank.toPairs bridge _ hcov
  intro pid comp ⟨fp, hfp, heq⟩
  have h1 : pid = fp.proposalId := (Prod.mk.inj heq).1
  have h2 : comp = fp.form := (Prod.mk.inj heq).2
  rw [h1, h2]
  exact hlink fp (soundRetention bank fp hfp)

/-! ## Direct 7A-lite composition -/

/-- Bank semantics equal chain exports intersected with admissibility, and the
    certified constructive scope lies in that set. -/
theorem direct_7A_lite_composition
    {SliceId Claim Question PId Compiled : Type*}
    [DecidableEq Claim]
    (df : DeploymentFrontier SliceId Claim Question)
    (hcert : CertifiedFrontier df)
    (M : AdmRegime Claim)
    (bank : CertifiedBank PId Compiled)
    (bridge : BankBridge PId Compiled Claim)
    (hlink : ∀ fp : FormalizedProposal PId Compiled,
      fp.passes bank.validator →
      bridge.realize fp.proposalId fp.form ∈
        Deploy (finsetProposer (chainExports df.chain)) M)
    (hcov : BankCoversDeployable bank.toPairs bridge
      (Deploy (finsetProposer (chainExports df.chain)) M)) :
    bankSemantics bank.toPairs bridge =
    { c | c ∈ chainExports df.chain } ∩ Adm M ∧
    { c | c ∈ df.scope.constructive } ∩ Adm M ⊆
    bankSemantics bank.toPairs bridge := by
  have hbank := direct_connector_4B _ M bank bridge hlink hcov
  constructor
  · exact hbank
  · rw [hbank]
    intro c ⟨hc_scope, hc_adm⟩
    exact ⟨certifiedFrontier_constructive_covered df hcert hc_scope, hc_adm⟩

/-- **Direct closure-bounded recombination**: combining two certified frontier
    proposers under one regime yields exactly the union of individual deployable
    sets. Stated over Problem 3's `DeploymentFrontier`. -/
theorem direct_closure_bounded_recombination
    {SliceId Claim Question : Type*} [DecidableEq Claim]
    (df₁ df₂ : DeploymentFrontier SliceId Claim Question)
    (M : AdmRegime Claim) :
    Deploy ((finsetProposer (chainExports df₁.chain)).combine
            (finsetProposer (chainExports df₂.chain))) M =
    Deploy (finsetProposer (chainExports df₁.chain)) M ∪
    Deploy (finsetProposer (chainExports df₂.chain)) M :=
  closure_bounded_recombination _ _ M

end SafeSlice
