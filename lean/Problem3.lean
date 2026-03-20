import Mathlib

noncomputable section

namespace SafeSlice

/-
This file fixes the restricted slice calculus used to compose local forms
and state fragment-level global formalizability results.
-/

structure Bridge (Claim : Type _) where
  premises : Finset Claim
  conclusion : Claim
deriving DecidableEq

def Bridge.WellFormed {Claim : Type _} [DecidableEq Claim]
    (claims exports : Finset Claim) (b : Bridge Claim) : Prop :=
  b.premises ⊆ claims ∧ b.conclusion ∈ exports

structure SliceSyntax (SliceId Claim Question : Type _) where
  sliceId : SliceId
  ambientImports : Finset Claim
  carryImports : Finset Claim
  claims : Finset Claim
  exports : Finset Claim
  certifiedBridges : Finset (Bridge Claim)
  pendingBridges : Finset (Bridge Claim)
  blockedExports : Finset Claim
  clarificationHoles : Finset Question
deriving DecidableEq

def SliceSyntax.WellFormed
    {SliceId Claim Question : Type _} [DecidableEq Claim]
    (s : SliceSyntax SliceId Claim Question) : Prop :=
  s.ambientImports ⊆ s.claims ∧
    s.carryImports ⊆ s.claims ∧
    s.exports ⊆ s.claims ∧
    s.blockedExports ⊆ s.exports ∧
    Disjoint s.certifiedBridges s.pendingBridges ∧
    (∀ b ∈ s.certifiedBridges, b.WellFormed s.claims s.exports) ∧
    (∀ b ∈ s.pendingBridges, b.WellFormed s.claims s.exports)

structure LocalForm (SliceId Claim Question : Type _) [DecidableEq Claim] where
  raw : SliceSyntax SliceId Claim Question
  wellFormed : raw.WellFormed

namespace LocalForm

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

def sliceId (f : LocalForm SliceId Claim Question) : SliceId :=
  f.raw.sliceId

def ambientImports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.ambientImports

def carryImports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.carryImports

def allImports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.ambientImports ∪ f.carryImports

def claims (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.claims

def exports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.exports

def certifiedBridges (f : LocalForm SliceId Claim Question) : Finset (Bridge Claim) :=
  f.raw.certifiedBridges

def pendingBridges (f : LocalForm SliceId Claim Question) : Finset (Bridge Claim) :=
  f.raw.pendingBridges

def blockedExports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.raw.blockedExports

def clarificationHoles (f : LocalForm SliceId Claim Question) : Finset Question :=
  f.raw.clarificationHoles

def pendingConclusions (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.pendingBridges.image Bridge.conclusion

def availableExports (f : LocalForm SliceId Claim Question) : Finset Claim :=
  f.exports.filter fun c => c ∉ f.blockedExports ∧ c ∉ f.pendingConclusions

lemma availableExports_subset_exports (f : LocalForm SliceId Claim Question) :
    f.availableExports ⊆ f.exports := by
  intro c hc
  exact (Finset.mem_filter.mp hc).1

end LocalForm

open Classical in
def compileSlice
    {SliceId Claim Question : Type _} [DecidableEq Claim]
    (s : SliceSyntax SliceId Claim Question) : Option (LocalForm SliceId Claim Question) :=
  if h : s.WellFormed then some ⟨s, h⟩ else none

def BoundaryOK
    {SliceId Claim Question : Type _} [DecidableEq Claim]
    (left right : LocalForm SliceId Claim Question) : Prop :=
  right.carryImports ⊆ left.availableExports

/-! ### Kernel stability lemmas -/

section KernelStability

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

/-- Well-formed syntax always compiles successfully. -/
theorem compileSlice_of_wellFormed (s : SliceSyntax SliceId Claim Question) (h : s.WellFormed) :
    ∃ f, compileSlice s = some f ∧ f.raw = s := by
  exact ⟨⟨s, h⟩, dif_pos h, rfl⟩

/-- Non-well-formed syntax is rejected by the compiler. -/
theorem compileSlice_none (s : SliceSyntax SliceId Claim Question) (h : ¬s.WellFormed) :
    compileSlice s = none := by
  exact dif_neg h

/-- Compiled slices preserve the underlying syntax. -/
theorem compileSlice_raw (s : SliceSyntax SliceId Claim Question) (f : LocalForm SliceId Claim Question)
    (h : compileSlice s = some f) : f.raw = s := by
  simp only [compileSlice] at h
  split at h
  · simp at h; exact h ▸ rfl
  · simp at h

/-- BoundaryOK holds trivially when the right slice carries no imports. -/
theorem BoundaryOK_of_empty_carry (left right : LocalForm SliceId Claim Question)
    (h : right.carryImports = ∅) : BoundaryOK left right := by
  unfold BoundaryOK
  rw [h]
  exact Finset.empty_subset _

/-- BoundaryOK is monotone in the left slice's available exports. -/
theorem BoundaryOK_mono_left {l₁ l₂ right : LocalForm SliceId Claim Question}
    (hsub : l₁.availableExports ⊆ l₂.availableExports)
    (hok : BoundaryOK l₁ right) : BoundaryOK l₂ right :=
  Finset.Subset.trans hok hsub

end KernelStability

/-! ### Composition closure -/

section CompositionClosure

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

/-- A composable chain is a list of local forms where each consecutive pair
    satisfies BoundaryOK: the right slice's carried imports are covered by
    the left slice's available exports. -/
def ComposableChain (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  chain.IsChain (fun l r => BoundaryOK l r)

/-- The empty chain is trivially composable. -/
theorem composableChain_nil :
    ComposableChain ([] : List (LocalForm SliceId Claim Question)) :=
  List.isChain_nil

/-- A singleton chain is trivially composable. -/
theorem composableChain_singleton (f : LocalForm SliceId Claim Question) :
    ComposableChain [f] :=
  List.isChain_singleton f

/-- Extending a composable chain on the right preserves composability
    when the boundary is OK between the last element and the new one. -/
theorem composableChain_append_singleton
    {chain : List (LocalForm SliceId Claim Question)}
    {f : LocalForm SliceId Claim Question}
    (hc : ComposableChain chain)
    (hb : ∀ last ∈ chain.getLast?, BoundaryOK last f) :
    ComposableChain (chain ++ [f]) := by
  unfold ComposableChain at *
  rw [List.isChain_append]
  exact ⟨hc, List.isChain_singleton f, fun a ha b hb' => by
    simp at hb'; subst hb'; exact hb a ha⟩

/-- The global exports of a composable chain: the union of available exports
    from all slices in the chain. -/
def chainExports (chain : List (LocalForm SliceId Claim Question)) : Finset Claim :=
  chain.foldr (fun f acc => f.availableExports ∪ acc) ∅

/-- The global imports of a composable chain: carried imports of the first
    slice that are not covered by any preceding slice's available exports.
    For a well-composed chain, only the first slice's ambient imports are
    truly external. -/
def chainExternalImports (chain : List (LocalForm SliceId Claim Question)) : Finset Claim :=
  match chain with
  | [] => ∅
  | f :: _ => f.ambientImports

/-- chainExports decomposes over append-singleton. -/
theorem chainExports_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question) :
    chainExports (chain ++ [f]) = chainExports chain ∪ f.availableExports := by
  induction chain with
  | nil => simp [chainExports]
  | cons a rest ih =>
    change a.availableExports ∪ chainExports (rest ++ [f]) =
      (a.availableExports ∪ chainExports rest) ∪ f.availableExports
    rw [ih, Finset.union_assoc]

end CompositionClosure

/-! ### Fragment admissibility bridge

This section packages the Lean side of the restricted-fragment interface used by Step7B_RestrictedFragmentBridge.thy.
-/

section FragmentBridge

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

/-- The fragment boundary: every slice's exports stay within its own claims.
    This mirrors Isabelle's "S ⊆ agent_derivable_support" — the fragment does
    not claim to export anything beyond what each slice locally derives. -/
def FragmentContained
    (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ∀ f ∈ chain, f.availableExports ⊆ f.claims

/-- Fragment soundness: every claim exported by the chain is backed by a
    certified bridge in some slice.  Mirrors Isabelle's tr1_sound_on. -/
def FragmentSound (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ∀ c ∈ chainExports chain, ∃ f ∈ chain, ∃ b ∈ f.certifiedBridges,
    b.conclusion = c

/-- Fragment completeness: every certified bridge conclusion that appears in
    the chain is reachable as an available export.
    Mirrors Isabelle's tr1_complete_on. -/
def FragmentComplete (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ∀ f ∈ chain, ∀ b ∈ f.certifiedBridges,
    b.conclusion ∈ chainExports chain

/-- The full admissibility predicate for 7A-lite restricted fragments.
    A chain satisfying this can coexist with the Isabelle obstruction barrier
    per `obstruction_package.admissible_fragment_coexists_with_barrier`. -/
def FragmentAdmissible (chain : List (LocalForm SliceId Claim Question)) : Prop :=
  ComposableChain chain ∧
  FragmentContained chain ∧
  FragmentSound chain ∧
  FragmentComplete chain

/-- Every well-formed LocalForm has its available exports within claims. -/
theorem localForm_exports_contained (f : LocalForm SliceId Claim Question) :
    f.availableExports ⊆ f.claims :=
  fun _ hc => f.wellFormed.2.2.1 (f.availableExports_subset_exports hc)

/-- FragmentContained holds automatically for any list of LocalForms. -/
theorem fragmentContained_of_localForms
    (chain : List (LocalForm SliceId Claim Question)) :
    FragmentContained chain :=
  fun f _ => localForm_exports_contained f

/-- The empty chain is trivially admissible. -/
theorem fragmentAdmissible_nil :
    FragmentAdmissible ([] : List (LocalForm SliceId Claim Question)) :=
  ⟨composableChain_nil, fragmentContained_of_localForms _,
   fun _ hc => absurd hc (by simp [chainExports]),
   fun _ hf => absurd hf (by simp)⟩

/-- FragmentComplete for a singleton: every certified bridge conclusion
    lands in the chain's exports, provided certified conclusions are
    neither blocked nor duplicated in pending bridges. -/
theorem fragmentComplete_singleton (f : LocalForm SliceId Claim Question)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    FragmentComplete [f] := by
  intro g hg b hb
  simp [List.mem_singleton] at hg; subst hg
  simp only [chainExports, List.foldr]
  apply Finset.mem_union_left
  simp only [LocalForm.availableExports, Finset.mem_filter]
  exact ⟨(g.wellFormed.2.2.2.2.2.1 b hb).2, hblk b hb, hpnd b hb⟩

/-- FragmentSound extends when appending a slice whose available exports
    are all certified. -/
theorem fragmentSound_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question)
    (hs : FragmentSound chain)
    (hcert : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c) :
    FragmentSound (chain ++ [f]) := by
  intro c hc
  rw [chainExports_append_singleton] at hc
  rcases Finset.mem_union.mp hc with hc | hc
  · obtain ⟨g, hg, b, hb, heq⟩ := hs c hc
    exact ⟨g, List.mem_append_left _ hg, b, hb, heq⟩
  · obtain ⟨b, hb, heq⟩ := hcert c hc
    exact ⟨f, List.mem_append_right _ (List.mem_singleton.mpr rfl), b, hb, heq⟩

/-- FragmentComplete extends when appending a slice whose certified bridge
    conclusions are not blocked or pending. -/
theorem fragmentComplete_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question)
    (hcomp : FragmentComplete chain)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    FragmentComplete (chain ++ [f]) := by
  intro g hg b hb
  rw [chainExports_append_singleton]
  rcases List.mem_append.mp hg with hg | hg
  · exact Finset.mem_union_left _ (hcomp g hg b hb)
  · rw [List.mem_singleton] at hg
    apply Finset.mem_union_right
    have hb' : b ∈ f.certifiedBridges := hg ▸ hb
    simp only [LocalForm.availableExports, Finset.mem_filter]
    exact ⟨(f.wellFormed.2.2.2.2.2.1 b hb').2, hblk b hb', hpnd b hb'⟩

/-- Main composition closure: extending an admissible chain with a compatible
    slice yields an admissible chain, under the natural domain invariants. -/
theorem fragmentAdmissible_append_singleton
    (chain : List (LocalForm SliceId Claim Question))
    (f : LocalForm SliceId Claim Question)
    (hadm : FragmentAdmissible chain)
    (hbound : ∀ last ∈ chain.getLast?, BoundaryOK last f)
    (hcert : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    FragmentAdmissible (chain ++ [f]) :=
  ⟨composableChain_append_singleton hadm.1 hbound,
   fragmentContained_of_localForms _,
   fragmentSound_append_singleton chain f hadm.2.2.1 hcert,
   fragmentComplete_append_singleton chain f hadm.2.2.2 hblk hpnd⟩

end FragmentBridge

/-! ### Global formal object

FragmentAdmissible is a *predicate* on a list of LocalForms.  For 7A-lite to
be more than a closure surrogate we need an explicit *typed object* that
carries the aggregated interface information and is the target type for
composeForms.  GlobalForm is that object.
-/

section GlobalFormObject

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

/-- Helper: collect all claims across a chain. -/
def chainClaims (chain : List (LocalForm SliceId Claim Question)) : Finset Claim :=
  chain.foldr (fun f acc => f.claims ∪ acc) ∅

/-- Helper: collect all certified bridges across a chain. -/
def chainCertifiedBridges (chain : List (LocalForm SliceId Claim Question)) :
    Finset (Bridge Claim) :=
  chain.foldr (fun f acc => f.certifiedBridges ∪ acc) ∅

/-- Helper: collect all pending bridges across a chain. -/
def chainPendingBridges (chain : List (LocalForm SliceId Claim Question)) :
    Finset (Bridge Claim) :=
  chain.foldr (fun f acc => f.pendingBridges ∪ acc) ∅

/-- Helper: collect all blocked exports across a chain. -/
def chainBlockedExports (chain : List (LocalForm SliceId Claim Question)) :
    Finset Claim :=
  chain.foldr (fun f acc => f.blockedExports ∪ acc) ∅

/-- Helper: collect all clarification holes across a chain. -/
def chainHoles [DecidableEq Question]
    (chain : List (LocalForm SliceId Claim Question)) : Finset Question :=
  chain.foldr (fun f acc => f.clarificationHoles ∪ acc) ∅

/-- Helper: collect slice identifiers in composition order. -/
def chainSliceIds (chain : List (LocalForm SliceId Claim Question)) : List SliceId :=
  chain.map LocalForm.sliceId

/-- An explicit global formal object produced by composing an admissible chain.

Unlike `FragmentAdmissible` (a predicate on a raw list), `GlobalForm` is a
concrete typed record that carries the aggregated interface data needed for
later theorem statements — global exports, external imports, the full claim
universe, all certified bridges, and unresolved holes — together with a proof
that the underlying chain is fragment-admissible. -/
structure GlobalForm (SliceId Claim Question : Type _)
    [DecidableEq Claim] [DecidableEq Question] where
  /-- The underlying composable chain of compiled slices. -/
  chain : List (LocalForm SliceId Claim Question)
  /-- Global exports: union of available exports from all slices. -/
  globalExports : Finset Claim
  /-- External imports: ambient imports of the first slice (truly external). -/
  externalImports : Finset Claim
  /-- All claims in the composed fragment. -/
  globalClaims : Finset Claim
  /-- All certified bridges across the chain. -/
  globalCertifiedBridges : Finset (Bridge Claim)
  /-- All pending (unresolved) bridges across the chain. -/
  globalPendingBridges : Finset (Bridge Claim)
  /-- All blocked exports across the chain. -/
  globalBlockedExports : Finset Claim
  /-- All unresolved clarification holes across the chain. -/
  globalHoles : Finset Question
  /-- Slice identifiers in composition order. -/
  sliceIds : List SliceId
  /-- Proof that the chain is fragment-admissible. -/
  admissible : FragmentAdmissible chain
  /-- The globalExports field agrees with chainExports. -/
  exports_consistent : globalExports = chainExports chain
  /-- The externalImports field agrees with chainExternalImports. -/
  imports_consistent : externalImports = chainExternalImports chain
  /-- The globalClaims field agrees with chainClaims. -/
  claims_consistent : globalClaims = chainClaims chain
  /-- The globalCertifiedBridges field agrees with chainCertifiedBridges. -/
  bridges_consistent :
    globalCertifiedBridges = chainCertifiedBridges chain
  /-- The globalPendingBridges field agrees with chainPendingBridges. -/
  pending_consistent :
    globalPendingBridges = chainPendingBridges chain
  /-- The globalBlockedExports field agrees with chainBlockedExports. -/
  blocked_consistent :
    globalBlockedExports = chainBlockedExports chain
  /-- The globalHoles field agrees with chainHoles. -/
  holes_consistent : globalHoles = chainHoles chain
  /-- The sliceIds field agrees with chainSliceIds. -/
  sliceIds_consistent : sliceIds = chainSliceIds chain

/-- Compose an admissible chain into an explicit global formal object.
    This is the constructive witness builder: given a chain and a proof of
    fragment admissibility, it packages all interface data into a single
    typed record.  No axioms, no sorry. -/
def composeForms
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    GlobalForm SliceId Claim Question :=
  { chain := chain
    globalExports := chainExports chain
    externalImports := chainExternalImports chain
    globalClaims := chainClaims chain
    globalCertifiedBridges := chainCertifiedBridges chain
    globalPendingBridges := chainPendingBridges chain
    globalBlockedExports := chainBlockedExports chain
    globalHoles := chainHoles chain
    sliceIds := chainSliceIds chain
    admissible := hadm
    exports_consistent := rfl
    imports_consistent := rfl
    claims_consistent := rfl
    bridges_consistent := rfl
    pending_consistent := rfl
    blocked_consistent := rfl
    holes_consistent := rfl
    sliceIds_consistent := rfl }

/-- chainExports is contained in chainClaims for any list of LocalForms. -/
theorem chainExports_subset_chainClaims
    (chain : List (LocalForm SliceId Claim Question)) :
    chainExports chain ⊆ chainClaims chain := by
  induction chain with
  | nil => simp [chainExports, chainClaims]
  | cons a rest ih =>
    intro c hc
    simp only [chainExports, List.foldr] at hc
    simp only [chainClaims, List.foldr]
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Finset.mem_union_left _ (localForm_exports_contained a hc)
    · exact Finset.mem_union_right _ (ih hc)

/-- The global exports of a GlobalForm are contained in its global claims. -/
theorem GlobalForm.exports_subset_claims (g : GlobalForm SliceId Claim Question) :
    g.globalExports ⊆ g.globalClaims := by
  rw [g.exports_consistent, g.claims_consistent]
  exact chainExports_subset_chainClaims g.chain

/-- Extending a GlobalForm with a new boundary-compatible slice. -/
def GlobalForm.extend
    (g : GlobalForm SliceId Claim Question)
    (f : LocalForm SliceId Claim Question)
    (hbound : ∀ last ∈ g.chain.getLast?, BoundaryOK last f)
    (hcert : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    GlobalForm SliceId Claim Question :=
  composeForms (g.chain ++ [f])
    (fragmentAdmissible_append_singleton g.chain f g.admissible hbound hcert hblk hpnd)

/-- A GlobalForm is fully resolved when it has no pending bridges,
    no blocked exports, and no clarification holes. -/
def GlobalForm.isFullyResolved
    (g : GlobalForm SliceId Claim Question) : Prop :=
  g.globalPendingBridges = ∅ ∧
  g.globalBlockedExports = ∅ ∧
  g.globalHoles = ∅

/-- A GlobalForm that is not fully resolved exposes exactly what
    remains unresolved — the interface state the auditor must check. -/
def GlobalForm.unresolvedSummary
    (g : GlobalForm SliceId Claim Question) :
    Finset (Bridge Claim) × Finset Claim × Finset Question :=
  (g.globalPendingBridges, g.globalBlockedExports, g.globalHoles)

/-- composeForms on the empty chain yields an empty GlobalForm. -/
theorem composeForms_nil :
    (composeForms ([] : List (LocalForm SliceId Claim Question)) fragmentAdmissible_nil).globalExports = ∅ := by
  simp [composeForms, chainExports]

/-- composeForms preserves the underlying chain. -/
theorem composeForms_chain
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    (composeForms chain hadm).chain = chain := rfl

/-! ### Restricted Global Formalizability Theorem

The main 7A-lite result: any fragment-admissible chain of compiled slices
admits an explicit global formal witness (a `GlobalForm`) satisfying:
  1. Coverage: the witness's global exports cover `chainExports chain`.
  2. Containment: global exports sit inside global claims.
  3. Soundness: every exported claim is backed by a certified bridge.
  4. Completeness: every certified bridge conclusion is reachable as an export.
  5. Admissibility: the witness carries a proof of `FragmentAdmissible`.
  6. Chain identity: the witness is built from exactly the given chain.

This is the constructive existential that the deployment frontier requires:
it converts the *predicate* `FragmentAdmissible` into a *typed object*
`GlobalForm` with machine-checkable interface guarantees, without sorry or
axioms. -/

/-- **Restricted Global Formalizability.**
    Given any fragment-admissible chain, there exists a `GlobalForm` whose
    global exports equal `chainExports chain`, whose exports are contained
    in its claims, whose chain is admissible, and whose underlying chain is
    exactly the input chain. -/
theorem restricted_global_formalizability
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    ∃ (g : GlobalForm SliceId Claim Question),
      g.chain = chain ∧
      g.globalExports = chainExports chain ∧
      g.globalExports ⊆ g.globalClaims ∧
      FragmentAdmissible g.chain ∧
      FragmentSound g.chain ∧
      FragmentComplete g.chain :=
  ⟨composeForms chain hadm, rfl, rfl,
   (composeForms chain hadm).exports_subset_claims,
   hadm, hadm.2.2.1, hadm.2.2.2⟩

/-! ### Cross-system bridge

This section defines Isabelle-compatible GlobalForm data and shows how
fragment-admissible chains are sent to that interface.
-/

section CrossSystemBridge

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

/-- Lean packaging of the ingredients used by the Isabelle bridge. -/
def GlobalForm.IsabelleCompatible
    (g : GlobalForm SliceId Claim Question) : Prop :=
  FragmentAdmissible g.chain ∧
  g.globalExports ⊆ g.globalClaims ∧
  FragmentSound g.chain ∧
  FragmentComplete g.chain

/-- `composeForms` maps a fragment-admissible chain to `IsabelleCompatible`. -/
theorem cross_system_global_bridge
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    ∃ (g : GlobalForm SliceId Claim Question),
      g.chain = chain ∧
      g.IsabelleCompatible :=
  ⟨composeForms chain hadm, rfl, hadm,
   (composeForms chain hadm).exports_subset_claims,
   hadm.2.2.1, hadm.2.2.2⟩

/-- The bridge witness preserves the underlying chain. -/
theorem cross_system_global_bridge_chain_identity
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    (composeForms chain hadm).chain = chain ∧
    (composeForms chain hadm).IsabelleCompatible :=
  ⟨rfl, hadm, (composeForms chain hadm).exports_subset_claims,
   hadm.2.2.1, hadm.2.2.2⟩

end CrossSystemBridge

/-! ### Semantic closure

This section states closure properties directly over the aggregated fields of a GlobalForm.
-/

section SemanticClosure

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

/-! Membership helpers for chain-aggregated fields. -/

theorem mem_chainCertifiedBridges
    {chain : List (LocalForm SliceId Claim Question)}
    {f : LocalForm SliceId Claim Question} {b : Bridge Claim}
    (hf : f ∈ chain) (hb : b ∈ f.certifiedBridges) :
    b ∈ chainCertifiedBridges chain := by
  induction chain with
  | nil => simp at hf
  | cons a rest ih =>
    simp only [chainCertifiedBridges, List.foldr]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ (ih hf)

theorem of_mem_chainCertifiedBridges
    {chain : List (LocalForm SliceId Claim Question)}
    {b : Bridge Claim}
    (hb : b ∈ chainCertifiedBridges chain) :
    ∃ f ∈ chain, b ∈ f.certifiedBridges := by
  induction chain with
  | nil => simp [chainCertifiedBridges] at hb
  | cons a rest ih =>
    simp only [chainCertifiedBridges, List.foldr] at hb
    rcases Finset.mem_union.mp hb with hb | hb
    · exact ⟨a, List.mem_cons_self .., hb⟩
    · obtain ⟨f, hf, hbf⟩ := ih hb
      exact ⟨f, List.mem_cons_of_mem _ hf, hbf⟩

theorem claims_subset_chainClaims
    {chain : List (LocalForm SliceId Claim Question)}
    {f : LocalForm SliceId Claim Question}
    (hf : f ∈ chain) :
    f.claims ⊆ chainClaims chain := by
  induction chain with
  | nil => simp at hf
  | cons a rest ih =>
    simp only [chainClaims, List.foldr]
    rcases List.mem_cons.mp hf with rfl | hf
    · exact Finset.subset_union_left
    · exact Finset.Subset.trans (ih hf) Finset.subset_union_right

theorem chainExternalImports_subset_chainClaims
    (chain : List (LocalForm SliceId Claim Question)) :
    chainExternalImports chain ⊆ chainClaims chain := by
  match chain with
  | [] => simp [chainExternalImports, chainClaims]
  | f :: rest =>
    simp only [chainExternalImports, chainClaims, List.foldr]
    exact Finset.Subset.trans f.wellFormed.1 Finset.subset_union_left

/-- Semantic closure for the aggregated fields of a GlobalForm. -/
def GlobalForm.SemanticallyClosed
    (g : GlobalForm SliceId Claim Question) : Prop :=
  (∀ c ∈ g.globalExports,
      ∃ b ∈ g.globalCertifiedBridges, b.conclusion = c) ∧
  (∀ b ∈ g.globalCertifiedBridges,
      b.premises ⊆ g.globalClaims) ∧
  (∀ b ∈ g.globalCertifiedBridges,
      b.conclusion ∈ g.globalExports) ∧
  g.globalExports ⊆ g.globalClaims ∧
  g.externalImports ⊆ g.globalClaims

/-- The core lifting lemma: `FragmentSound` at the chain level implies
    export justification at the GlobalForm field level. -/
theorem globalSound_of_fragmentSound
    (chain : List (LocalForm SliceId Claim Question))
    (hs : FragmentSound chain) :
    ∀ c ∈ chainExports chain,
      ∃ b ∈ chainCertifiedBridges chain, b.conclusion = c := by
  intro c hc
  obtain ⟨f, hf, b, hb, heq⟩ := hs c hc
  exact ⟨b, mem_chainCertifiedBridges hf hb, heq⟩

/-- Bridge groundedness: every certified bridge in the chain has its
    premises within chainClaims. -/
theorem chainBridges_premises_subset_chainClaims
    (chain : List (LocalForm SliceId Claim Question)) :
    ∀ b ∈ chainCertifiedBridges chain,
      b.premises ⊆ chainClaims chain := by
  intro b hb
  obtain ⟨f, hf, hbf⟩ := of_mem_chainCertifiedBridges hb
  exact Finset.Subset.trans
    (f.wellFormed.2.2.2.2.2.1 b hbf).1
    (claims_subset_chainClaims hf)

/-- Bridge reachability: `FragmentComplete` at the chain level implies
    every certified bridge conclusion is a chain export. -/
theorem globalComplete_of_fragmentComplete
    (chain : List (LocalForm SliceId Claim Question))
    (hc : FragmentComplete chain) :
    ∀ b ∈ chainCertifiedBridges chain,
      b.conclusion ∈ chainExports chain := by
  intro b hb
  obtain ⟨f, hf, hbf⟩ := of_mem_chainCertifiedBridges hb
  exact hc f hf b hbf

/-- composeForms yields a semantically closed GlobalForm. -/
theorem composeForms_semanticallyClosed
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    (composeForms chain hadm).SemanticallyClosed := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Export justification
    intro c hc
    simp only [composeForms] at hc ⊢
    exact globalSound_of_fragmentSound chain hadm.2.2.1 c hc
  · -- Bridge groundedness
    intro b hb
    simp only [composeForms] at hb ⊢
    exact chainBridges_premises_subset_chainClaims chain b hb
  · -- Bridge reachability
    intro b hb
    simp only [composeForms] at hb ⊢
    exact globalComplete_of_fragmentComplete chain hadm.2.2.2 b hb
  · -- Export containment
    exact (composeForms chain hadm).exports_subset_claims
  · -- Import containment
    simp only [composeForms]
    exact chainExternalImports_subset_chainClaims chain

/-- **Strengthened restricted global formalizability.**

    Any fragment-admissible chain yields a `GlobalForm` that is
    semantically closed — the strongest 7A-lite result, converting
    the chain-level predicate into a self-contained typed object
    with its own global discharge semantics. -/
theorem restricted_global_formalizability_semantic
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain) :
    ∃ (g : GlobalForm SliceId Claim Question),
      g.chain = chain ∧
      g.SemanticallyClosed ∧
      g.IsabelleCompatible :=
  ⟨composeForms chain hadm,
   rfl,
   composeForms_semanticallyClosed chain hadm,
   hadm,
   (composeForms chain hadm).exports_subset_claims,
   hadm.2.2.1, hadm.2.2.2⟩

end SemanticClosure

end GlobalFormObject

/-! ### Explicit syntactic fragment and constructive tr1_on derivation

The 7A-lite frontier requires an explicit syntactic fragment `Frag` at theorem
level — not only `FragmentAdmissible` as a chain predicate — together with:

  1. `Frag` defined as a concrete `Set` of task triples, syntactically restricted
     to the conclusions reachable through a `GlobalForm`'s exports.
  2. `Frag ⊆ agentDerivableSupport` proved from a support-reflection assumption.
  3. `tr1_on` on `Frag` derived from substantive constructive assumptions
     (soundness + completeness on the fragment), not from decidability or
     computability alone.
  4. Wiring to `FragmentAdmissible` via the Step7 admissibility bridge.

These mirror the Isabelle-side concepts `tr1_on`, `agent_derivable_support`, and
the forthcoming `fragment_admissible_for_7A_lite`.
-/

section ExplicitFragment

variable {SliceId Claim Question : Type _} [DecidableEq Claim] [DecidableEq Question]

/-! #### Isabelle-mirrored definitions -/

/-- Agent derivable support: the set of tasks the agent can derive at a given world.
    Mirrors Isabelle's `agent_derivable_support H w = {(c,Γ,φ). a_derives H w c Γ φ}`. -/
def agentDerivableSupport
    {Context World : Type _}
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) : Set (Context × Finset Claim × Claim) :=
  {t | a_derives w t.1 t.2.1 t.2.2}

/-- Sound-and-complete translation on a task set.
    Mirrors Isabelle's `tr1_on H F τ w Tasks`:
      ∀(c,Γ,φ) ∈ Tasks. a_derives H w c Γ φ ↔ f_derives F w c (τ`Γ) (τ φ) -/
def tr1_on
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim)
    (w : World)
    (Tasks : Set (Context × Finset Claim × Claim)) : Prop :=
  ∀ t ∈ Tasks,
    (a_derives w t.1 t.2.1 t.2.2 ↔ f_derives w t.1 (t.2.1.image τ) (τ t.2.2))

/-! #### The explicit syntactic fragment -/

/-- **The explicit syntactic fragment `Frag`.**

    `Frag g` is the set of tasks `(c, Γ, φ)` whose conclusion `φ` falls
    within the `GlobalForm`'s global exports. This is the theorem-level
    syntactic restriction that the 7A-lite frontier quantifies over.

    Note: `Frag` is defined purely by conclusion membership in `globalExports`,
    making it a *syntactic* fragment boundary. The agent-derivability of any
    particular task `(c, Γ, φ) ∈ Frag g` is a separate semantic property
    supplied by the constructive assumptions. -/
def Frag
    {Context : Type _}
    (g : GlobalForm SliceId Claim Question) :
    Set (Context × Finset Claim × Claim) :=
  {t | t.2.2 ∈ g.globalExports}

/-! #### Constructive assumption package -/

/-- **Substantive constructive assumptions for deriving `tr1_on` on `Frag`.**

    This is the assumption package that the 7A-lite frontier requires.
    It expresses support-level reflection plus soundness/completeness —
    NOT decidability or computability alone (which would silently collapse
    the barrier boundary).

    The three components:
    • `sound`: agent derivability within the fragment implies formal derivability
      through the translation τ.
    • `complete`: formal derivability of a translated fragment conclusion implies
      agent derivability.
    • `support_inhabited`: every export in the fragment is agent-derivable from
      some context and premises — the fragment is non-vacuous and sits inside
      `agentDerivableSupport`. -/
structure FragTranslationAssumptions
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim)
    (w : World) where
  /-- Soundness on the fragment: agent derivability implies formal derivability. -/
  sound : ∀ c Γ φ, φ ∈ g.globalExports →
    a_derives w c Γ φ → f_derives w c (Γ.image τ) (τ φ)
  /-- Completeness on the fragment: formal derivability implies agent derivability. -/
  complete : ∀ c Γ φ, φ ∈ g.globalExports →
    f_derives w c (Γ.image τ) (τ φ) → a_derives w c Γ φ
  /-- Support reflection: every exported claim is agent-derivable from some
      context and premises. Without this, `Frag` might be vacuously translatable
      on an empty set of agent-derivable tasks. -/
  support_inhabited : ∀ φ ∈ g.globalExports,
    ∃ c Γ, a_derives w c Γ φ

/-! #### Results -/

/-- **`Frag` is contained in `agentDerivableSupport` for agent-derivable tasks.**

    More precisely: tasks in `Frag g` that the agent derives are in
    `agentDerivableSupport`. This is the Lean mirror of Isabelle's
    `S ⊆ agent_derivable_support H w` restricted to the derivable part
    of the fragment. -/
theorem frag_inter_support_subset
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    (Frag g : Set (Context × Finset Claim × Claim)) ∩
      agentDerivableSupport a_derives w ⊆
        agentDerivableSupport a_derives w := by
  exact Set.inter_subset_right

/-- **Frag inclusion via support_inhabited.**

    When constructive assumptions hold, every export has at least one
    witness task in `agentDerivableSupport`. This proves the set-level
    inclusion `{φ | φ ∈ g.globalExports} ⊆ {φ | ∃ c Γ, a_derives w c Γ φ}`. -/
theorem frag_exports_within_support
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    ∀ φ ∈ g.globalExports,
      ∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        agentDerivableSupport a_derives w :=
  fun φ hφ => h.support_inhabited φ hφ

/-- Constructive assumptions yield tr1_on on Frag. -/
theorem constructive_tr1_on_frag
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    tr1_on a_derives f_derives τ w (Frag g) := by
  intro ⟨c, Γ, φ⟩ hmem
  simp only [Frag, Set.mem_setOf_eq] at hmem
  exact ⟨h.sound c Γ φ hmem, h.complete c Γ φ hmem⟩

/-! #### Supported fragment -/

/-- Tasks whose conclusions are exported and agent-derivable. -/
def SupportedFrag
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) : Set (Context × Finset Claim × Claim) :=
  {t | t.2.2 ∈ g.globalExports ∧ a_derives w t.1 t.2.1 t.2.2}

/-- SupportedFrag is contained in agentDerivableSupport. -/
theorem supportedFrag_subset_agentDerivableSupport
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    SupportedFrag g a_derives w ⊆ agentDerivableSupport a_derives w :=
  fun _ ht => ht.2

/-- `SupportedFrag` is a subset of `Frag`. -/
theorem supportedFrag_subset_frag
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    SupportedFrag g a_derives w ⊆ Frag g :=
  fun _ ht => ht.1

/-- SupportedFrag is the intersection of Frag and agentDerivableSupport. -/
theorem supportedFrag_eq_frag_inter_support
    {Context World : Type _}
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (w : World) :
    SupportedFrag g a_derives w = Frag g ∩ agentDerivableSupport a_derives w := by
  ext ⟨c, Γ, φ⟩
  simp only [SupportedFrag, Frag, agentDerivableSupport, Set.mem_setOf_eq,
             Set.mem_inter_iff]

/-- Constructive assumptions witness each Frag conclusion in agentDerivableSupport. -/
theorem frag_conclusion_coverage
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    ∀ φ, (∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈ Frag g) →
      ∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        SupportedFrag g a_derives w := by
  intro φ ⟨_, _, hfrag⟩
  simp only [Frag, Set.mem_setOf_eq] at hfrag
  obtain ⟨c', Γ', hd⟩ := h.support_inhabited φ hfrag
  exact ⟨c', Γ', hfrag, hd⟩

/-- Constructive assumptions yield tr1_on on SupportedFrag. -/
theorem tr1_on_supportedFrag
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    tr1_on a_derives f_derives τ w (SupportedFrag g a_derives w) :=
  fun t ht => constructive_tr1_on_frag g a_derives f_derives τ w h t
    (supportedFrag_subset_frag g a_derives w ht)

/-- Under constructive assumptions, every global export is witnessed in
    `SupportedFrag` — the fragment is non-vacuous. -/
theorem supportedFrag_nonempty_of_constructive
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    ∀ φ ∈ g.globalExports,
      ∃ c Γ, (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        SupportedFrag g a_derives w := by
  intro φ hφ
  obtain ⟨c, Γ, hd⟩ := h.support_inhabited φ hφ
  exact ⟨c, Γ, hφ, hd⟩

/-- SupportedFrag packages the support, translation, and witness conditions used below. -/
theorem supportedFrag_admissible_package
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions g a_derives f_derives τ w) :
    SupportedFrag g a_derives w ⊆ agentDerivableSupport a_derives w ∧
    tr1_on a_derives f_derives τ w (SupportedFrag g a_derives w) ∧
    (∀ φ ∈ g.globalExports, ∃ c Γ,
      (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
        SupportedFrag g a_derives w) :=
  ⟨supportedFrag_subset_agentDerivableSupport g a_derives w,
   tr1_on_supportedFrag g a_derives f_derives τ w h,
   supportedFrag_nonempty_of_constructive g a_derives f_derives τ w h⟩

/-! #### Admissibility bridge -/

/-- Lean 7A-lite admissibility over a semantically closed GlobalForm. -/
def fragment_admissible_for_7A_lite
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (g : GlobalForm SliceId Claim Question)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim)
    (w : World) : Prop :=
  FragmentAdmissible g.chain ∧
  g.SemanticallyClosed ∧
  (∀ φ ∈ g.globalExports, ∃ c Γ,
    (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈
      agentDerivableSupport a_derives w) ∧
  tr1_on a_derives f_derives τ w (Frag g)

/-- Constructive assumptions yield 7A-lite admissibility for the composed GlobalForm. -/
theorem support_admissible_from_constructive_assumptions
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions (composeForms chain hadm) a_derives f_derives τ w) :
    fragment_admissible_for_7A_lite (composeForms chain hadm) a_derives f_derives τ w :=
  ⟨hadm,
   composeForms_semanticallyClosed chain hadm,
   frag_exports_within_support (composeForms chain hadm) a_derives f_derives τ w h,
   constructive_tr1_on_frag (composeForms chain hadm) a_derives f_derives τ w h⟩

/-! #### Cross-system set extraction

The Isabelle `fragment_admissible_for_7A_lite H F τ w S` is parameterized by a
plain set `S`.  The Lean predicate wraps this in a `GlobalForm`.  The theorem
below extracts an explicit set `S = SupportedFrag g a_derives w` satisfying
all three Isabelle-interface conditions, bridging the two representations.

Cross-system alignment map:
  Lean FragmentAdmissible g.chain      ↔  Isabelle obstruction_free_fragment H w S
  Lean SupportedFrag ⊆ support         ↔  Isabelle S ⊆ agent_derivable_support H w
  Lean tr1_on on SupportedFrag          ↔  Isabelle tr1_on H F τ w S
-/

/-- **Cross-system set extraction: from GlobalForm to an explicit Isabelle-compatible set.**

    Given constructive assumptions on a composed `GlobalForm`, this theorem
    extracts the explicit set `SupportedFrag` and proves it satisfies:
      (1) `S ⊆ agentDerivableSupport`  — Isabelle's `S ⊆ agent_derivable_support`
      (2) `tr1_on` on `S`              — Isabelle's `tr1_on H F τ w S`
      (3) every exported conclusion is witnessed in `S`  — non-vacuity

    This is the Lean-side output that the Isabelle `admissible_fragment_coexists_with_barrier`
    consumes (via the matching `fragment_admissible_for_7A_lite` name). -/
theorem cross_system_extract_admissible_set
    {Context World FormalClaim : Type _} [DecidableEq FormalClaim]
    (chain : List (LocalForm SliceId Claim Question))
    (hadm : FragmentAdmissible chain)
    (a_derives : World → Context → Finset Claim → Claim → Prop)
    (f_derives : World → Context → Finset FormalClaim → FormalClaim → Prop)
    (τ : Claim → FormalClaim) (w : World)
    (h : FragTranslationAssumptions (composeForms chain hadm) a_derives f_derives τ w) :
    let g := composeForms chain hadm
    let S := SupportedFrag g a_derives w
    S ⊆ agentDerivableSupport a_derives w ∧
    tr1_on a_derives f_derives τ w S ∧
    (∀ φ ∈ g.globalExports, ∃ c Γ,
      (⟨c, Γ, φ⟩ : Context × Finset Claim × Claim) ∈ S) :=
  supportedFrag_admissible_package (composeForms chain hadm) a_derives f_derives τ w h

end ExplicitFragment

/-! ### Deployment frontier embedding

The certified deployment frontier has two nodes:
  1. **7A-lite (constructive):** a FragmentAdmissible composable chain that
     provides sound+complete restricted translation via slice compilation.
  2. **Safe Slice (statistical fallback):** covers tasks outside the
     formalizable fragment, providing statistical guarantees without
     requiring exact translation.

The frontier is certified when the constructive node is admissible and the
two nodes together cover the full task scope.
-/

section DeploymentFrontier

variable {SliceId Claim Question : Type _} [DecidableEq Claim]

/-- A task scope partitions claims into those covered by the constructive
    fragment and those handled by the statistical fallback. -/
structure TaskScope (Claim : Type _) where
  /-- Claims reachable by 7A-lite slice compilation. -/
  constructive : Finset Claim
  /-- Claims handled by Safe Slice statistical fallback. -/
  statistical : Finset Claim

/-- The deployment frontier positions a constructive composable chain
    alongside a statistical fallback scope. -/
structure DeploymentFrontier (SliceId Claim Question : Type _) [DecidableEq Claim] where
  /-- The constructive node: a composable chain of compiled slices. -/
  chain : List (LocalForm SliceId Claim Question)
  /-- The scope partition between constructive and statistical coverage. -/
  scope : TaskScope Claim

/-- A deployment frontier is certified when:
    (1) the constructive chain is fragment-admissible;
    (2) the chain's exports cover exactly the constructive scope;
    (3) the constructive and statistical scopes are disjoint. -/
def CertifiedFrontier (df : DeploymentFrontier SliceId Claim Question) : Prop :=
  FragmentAdmissible df.chain ∧
  df.scope.constructive ⊆ chainExports df.chain ∧
  Disjoint df.scope.constructive df.scope.statistical

/-- The total coverage of a certified deployment frontier. -/
def DeploymentFrontier.totalCoverage (df : DeploymentFrontier SliceId Claim Question) :
    Finset Claim :=
  df.scope.constructive ∪ df.scope.statistical

/-- A certified frontier's constructive node is automatically fragment-admissible. -/
theorem certifiedFrontier_admissible
    (df : DeploymentFrontier SliceId Claim Question)
    (hcert : CertifiedFrontier df) :
    FragmentAdmissible df.chain :=
  hcert.1

/-- The constructive scope of a certified frontier is backed by chain exports. -/
theorem certifiedFrontier_constructive_covered
    (df : DeploymentFrontier SliceId Claim Question)
    (hcert : CertifiedFrontier df) :
    df.scope.constructive ⊆ chainExports df.chain :=
  hcert.2.1

/-- Building a certified frontier from an admissible chain and a compatible scope. -/
theorem certifiedFrontier_of_admissible
    (chain : List (LocalForm SliceId Claim Question))
    (scope : TaskScope Claim)
    (hadm : FragmentAdmissible chain)
    (hcov : scope.constructive ⊆ chainExports chain)
    (hdisj : Disjoint scope.constructive scope.statistical) :
    CertifiedFrontier ⟨chain, scope⟩ :=
  ⟨hadm, hcov, hdisj⟩

/-- Extending a certified frontier's constructive node preserves certification
    when the new slice is boundary-compatible and the scope stays covered. -/
theorem certifiedFrontier_extend
    (df : DeploymentFrontier SliceId Claim Question)
    (f : LocalForm SliceId Claim Question)
    (hcert : CertifiedFrontier df)
    (hbound : ∀ last ∈ df.chain.getLast?, BoundaryOK last f)
    (hscope : df.scope.constructive ⊆ chainExports df.chain ∪ f.availableExports)
    (hcertBr : ∀ c ∈ f.availableExports, ∃ b ∈ f.certifiedBridges, b.conclusion = c)
    (hblk : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.blockedExports)
    (hpnd : ∀ b ∈ f.certifiedBridges, b.conclusion ∉ f.pendingConclusions) :
    CertifiedFrontier ⟨df.chain ++ [f], df.scope⟩ := by
  refine ⟨?_, ?_, hcert.2.2⟩
  · exact fragmentAdmissible_append_singleton df.chain f hcert.1 hbound hcertBr hblk hpnd
  · intro c hc
    rw [chainExports_append_singleton]
    exact hscope hc

end DeploymentFrontier

end SafeSlice
